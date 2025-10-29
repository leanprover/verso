/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc
import Verso.Doc.Concrete.InlineString
import Verso.Doc.Lsp

namespace Verso.Doc.Concrete

open Lean Verso Parser Doc Elab

def document : Parser where
  fn := atomicFn <| Verso.Parser.document (blockContext := {maxDirective := some 6})

@[combinator_parenthesizer document] def document.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter document] def document.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

def termDocument : Parser where
  fn := (atomicFn doc) >> whitespace
where
  doc : ParserFn := fun c s =>
    let opener := s.stxStack.back
    let indent := opener.getHeadInfo.getPos!
    let col := c.fileMap.toPosition indent |>.column

    let opener := getOpener opener
    if opener.isEmpty || opener.any (· ≠ ':') || opener.length < 3 then
      s.mkError s!"document after at least three colons (got {opener.quote})"
    else
      Verso.Parser.document (blockContext := {maxDirective := some (opener.length - 1), minIndent := col}) c s

  getOpener : Syntax → String
    | .node _ _ #[stx] => getOpener stx
    | .atom _ v => v
    | _ => ""

@[combinator_parenthesizer termDocument] def termDocument.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter termDocument] def termDocument.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

/-- Advance the parser to EOF on failure so Lean doesn't try to parse further commands -/
def completeDocument : Parser where
  fn := (Lean.Parser.recoverFn Verso.Parser.document fun _ => skipFn) >> untilEoi
where
  untilEoi : ParserFn := fun c s =>
    s.setPos c.endPos

@[combinator_parenthesizer completeDocument] def completeDocument.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter completeDocument] def completeDocument.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

partial def findGenreTm : Syntax → TermElabM Unit
  | `($g:ident) => discard <| realizeGlobalConstNoOverloadWithInfo g -- Don't allow it to become an auto-argument
  | `(($e)) => findGenreTm e
  | _ => pure ()

partial def findGenreCmd (genre : Syntax) : Command.CommandElabM Unit :=
  Command.runTermElabM fun _ => findGenreTm genre

def saveRefs [Monad m] [MonadInfoTree m] (st : DocElabM.State) (st' : PartElabM.State) : m Unit := do
  for r in internalRefs st'.linkDefs st.linkRefs do
    for stx in r.syntax do
      pushInfoLeaf <| .ofCustomInfo {stx := stx , value := Dynamic.mk r}
  for r in internalRefs st'.footnoteDefs st.footnoteRefs do
    for stx in r.syntax do
      pushInfoLeaf <| .ofCustomInfo {stx := stx , value := Dynamic.mk r}

private def elabGenre (genre : TSyntax `term) : TermElabM Expr :=
  Term.elabTerm genre (some (.const ``Doc.Genre []))

/--
All-at-once elaboration of verso document syntax to syntax denoting a verso `Part`. Implements
elaboration of the `#docs` command and `#doc` term. The `#doc` command is incremental, and thus
splits the logic in this function across multiple functions.
-/
private def elabDoc (genre: Term) (title: StrLit) (topLevelBlocks : Array Syntax) (endPos: String.Pos.Raw) : TermElabM Term := do
  let env ← getEnv
  let titleParts ← stringToInlines title
  let titleString := inlinesToString env titleParts
  let initDocState : DocElabM.State := {}
  let initPartState : PartElabM.State := .init (.node .none nullKind titleParts)

  let ((), docElabState, partElabState) ←
    PartElabM.run genre (← elabGenre genre) initDocState initPartState <| do
      let mut errors := #[]
      PartElabM.setTitle titleString (← PartElabM.liftDocElabM <| titleParts.mapM (elabInline ⟨·⟩))
      for b in topLevelBlocks do
        try
          partCommand ⟨b⟩
        catch e =>
          errors := errors.push e
      closePartsUntil 0 endPos
      for e in errors do
        match e with
        | .error stx msg => logErrorAt stx msg
        | oops@(.internal _ _) => throw oops
      pure ()
  saveRefs docElabState partElabState

  let finished := partElabState.partContext.toPartFrame.close endPos

  pushInfoLeaf <| .ofCustomInfo {stx := (← getRef) , value := Dynamic.mk finished.toTOC}
  finished.toVersoDoc genre

elab "#docs" "(" genre:term ")" n:ident title:str ":=" ":::::::" text:document ":::::::" : command => do
  findGenreCmd genre
  let endTok :=
    match ← getRef with
    | .node _ _ t =>
      match t.back? with
      | some x => x
      | none => panic! "No final token!"
    | _ => panic! "Nothing"
  let doc ← Command.runTermElabM fun _ => elabDoc genre title text.raw.getArgs endTok.getPos!
  Command.elabCommand (← `(def $n : VersoDoc $genre := $doc))

syntax docTermBody :=
  atomic(":::" termDocument ":::") <|>
  atomic("::::" termDocument "::::") <|>
  atomic(":::::" termDocument ":::::") <|>
  atomic("::::::" termDocument "::::::") <|>
  atomic(":::::::" termDocument ":::::::") <|>
  atomic("::::::::" termDocument "::::::::") <|>
  atomic(":::::::::" termDocument ":::::::::") <|>
  atomic("::::::::::" termDocument "::::::::::") <|>
  atomic(":::::::::::" termDocument ":::::::::::")

/--
Elaborates a Verso document in a term position. There are two forms:

verso "TITLE"
-/
scoped syntax (name := docTerm) "verso " ("(" term ")")? str docTermBody : term

open Elab Term in
elab_rules : term
  | `(verso $[($genre)]? $title:str $body:docTermBody) => do
  genre.forM (findGenreTm ·.raw)
  let genre ←
    if let some g := genre then
      findGenreTm g.raw
      pure g
    else
      `((_ : Genre))
  let endPos := body.raw.getTailPos? |>.getD (← getFileMap).source.endPos
  let docu ← elabDoc genre title body.raw[0][1].getArgs endPos
  Term.elabTerm (← ``( ($(docu) : VersoDoc $genre))) none


elab "#doc" "(" genre:term ")" title:str "=>" text:completeDocument eoi : term => do
  findGenreTm genre
  let endPos := (← getFileMap).source.endPos
  let doc ← elabDoc genre title text.raw.getArgs endPos
  Term.elabTerm (← `( ($(doc) : Part $genre))) none


scoped syntax (name := addBlockCmd) block term:max : command
scoped syntax (name := addLastBlockCmd) block term:max str : command

/-!
Unlike `#doc` expressions and `#docs` commands, which are elaborated all at once, `#doc` commands
are elaborated top-level-block by top-level-block in the manner of Lean's commands. This is done by
replacing the parser for the `command` category:
-/

/-- Replaces the stored parsing behavior for the category `cat` with the behavior defined by `p`. -/
private def replaceCategoryParser (cat : Name) (p : ParserFn) : Command.CommandElabM Unit :=
  modifyEnv (categoryParserFnExtension.modifyState · fun st =>
    fun n => if n == cat then p else st n)

/--
Parses each top-level block as either an `addBlockCmd` or an `addLastBlockCmd`. (This is what
Verso uses to replace the command parser.)
-/
private def versoBlockCommandFn (genre : Term) (title : String) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let s := recoverBlockWith #[.missing] (Verso.Parser.block {}) c s
  if s.hasError then s
  else
    let s := s.pushSyntax genre
    let s := ignoreFn (manyFn blankLine) c s
    let i := s.pos
    if c.atEnd i then
      let s := s.pushSyntax (Syntax.mkStrLit title)
      s.mkNode ``addLastBlockCmd iniSz
    else
      s.mkNode ``addBlockCmd iniSz

/-!
As we elaborate a `#doc` command top-level-block by top-level-block, the Lean environment will
be used to thread state between the separate top level blocks. These three environment extensions:
`docStateExt`, `partStateExt`, and `originalCatParserExt`, contain the state that needs to exist
across top-level-block parsing events.
-/

initialize docStateExt : EnvExtension DocElabM.State ← registerEnvExtension (pure {})
initialize partStateExt : EnvExtension (Option PartElabM.State) ← registerEnvExtension (pure none)
/--
The original parser for the `command` category, which is restored while elaborating a Verso block so
that nested Lean code has the correct syntax.
-/
initialize originalCatParserExt : EnvExtension CategoryParserFn ← registerEnvExtension (pure <| fun _ => whitespace)

/--
Performs `PartElabM.run` with state gathered from `docStateExt` and `partStateExt`, and then updates
the state in those environment extensions with any modifications. Also replaces the default command
parser in case `act` wants to parse commands (such as within an embedded code block).
-/
private def runPartElabInEnv (genreSyntax: Term) (act : PartElabM a) : Command.CommandElabM a := do
  let env ← getEnv
  let versoCmdFn := categoryParserFnExtension.getState env
  let docState := docStateExt.getState env
  let some partState := partStateExt.getState env
    | panic! "The document's start state is not initialized"

  try
    modifyEnv (fun env => categoryParserFnExtension.setState env <| originalCatParserExt.getState env)
    let (result, docState', partState') ← Command.runTermElabM fun _ => do
      PartElabM.run genreSyntax (← elabGenre genreSyntax) docState partState act
    modifyEnv (docStateExt.setState · docState')
    modifyEnv (partStateExt.setState · (some partState'))
    return result
  finally
    modifyEnv (categoryParserFnExtension.setState · versoCmdFn)

private def saveRefsInEnv : Command.CommandElabM Unit := do
  let env ← getEnv
  let docState := docStateExt.getState env
  let some partState := partStateExt.getState env
    | panic! "The document's start state is not initialized"
  saveRefs docState partState

/-!
When we do incremental parsing of `#doc` commands, we split the behaviors that are done all at once
in `elabDoc` across three functions: the prelude in `startDoc`, the loop body in `runVersoBlock`,
and the postlude in `finishDoc`.
-/

private def startDoc (genre : Term) (title: StrLit) : Command.CommandElabM String := do
  let env ← getEnv
  let titleParts ← stringToInlines title
  let titleString := inlinesToString env titleParts
  let initDocState : DocElabM.State := {}
  let initPartState : PartElabM.State := .init (.node .none nullKind titleParts)

  modifyEnv (docStateExt.setState · initDocState)
  modifyEnv (partStateExt.setState · (some initPartState))
  runPartElabInEnv genre <| do
    PartElabM.setTitle titleString (← PartElabM.liftDocElabM <| titleParts.mapM (elabInline ⟨·⟩))
  return titleString

private def runVersoBlock (genre : Term) (block : TSyntax `block) : Command.CommandElabM Unit := do
  runPartElabInEnv genre <| partCommand block
  -- This calls pushInfoLeaf a quadratic number of times for a for a linear number of top-level
  -- verso blocks, which should be harmless but may be inefficient. It may be desirable to tag
  -- info leaves that have already been pushed to avoid pushing them again.
  saveRefsInEnv

private def finishDoc (genre : Term) (title : StrLit) : Command.CommandElabM Unit:= do
  let endPos := (← getFileMap).source.endPos
  runPartElabInEnv genre <| do closePartsUntil 0 endPos

  let env ← getEnv
  let some partElabState := partStateExt.getState env
    | panic! "The document's start state was never initialized"
  let finished := partElabState.partContext.toPartFrame.close endPos

  let n := mkIdentFrom title (← currentDocName)
  let doc ← finished.toVersoDoc genre
  let ty ← ``(VersoDoc $genre)
  Command.elabCommand (← `(def $n : $ty := $doc))

syntax (name := replaceDoc) "#doc" "(" term ")" str "=>" : command
elab_rules : command
  | `(command|#doc ( $genre:term ) $title:str =>%$tok) => open Lean Parser Elab Command in do
  findGenreCmd genre
  elabCommand <| ← `(open scoped Lean.Doc.Syntax)

  let titleString ← startDoc genre title

  -- Sets up basic incremental evaluation of documents by replacing Lean's command-by-command parser
  -- with a top-level-block parser.
  modifyEnv fun env => originalCatParserExt.setState env (categoryParserFnExtension.getState env)
  replaceCategoryParser `command (versoBlockCommandFn genre titleString)

  -- Edge case: if there's no blocks after the =>, the replacement command parser won't get called,
  -- so we detect that case and call finishDoc.
  if let some stopPos := tok.getTailPos? then
    let txt ← getFileMap
    if stopPos.extract txt.source txt.source.endPos |>.all (·.isWhitespace) then
      finishDoc genre title

@[command_elab addBlockCmd]
def elabVersoBlock : Command.CommandElab
  | `(addBlockCmd| $b:block $genre:term) => do
    runVersoBlock genre b
  | _ => throwUnsupportedSyntax

@[command_elab addLastBlockCmd]
def elabVersoLastBlock : Command.CommandElab
  | `(addLastBlockCmd| $b:block $genre:term $title:str) => do
    runVersoBlock genre b
    -- Finish up the document
    finishDoc genre title
  | _ => throwUnsupportedSyntax
