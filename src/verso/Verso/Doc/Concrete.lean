/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Parser.Types
public meta import Verso.Parser
public import Lean.Elab.Command
public meta import SubVerso.Highlighting.Export
import Verso.Doc
public import Verso.Doc.Elab
public meta import Verso.Doc.Elab.Monad
import Verso.Doc.Concrete.InlineString
import Verso.Doc.Lsp

namespace Verso.Doc.Concrete

open Lean Verso Parser Doc Elab

/-- The text of the delimiter that opened a document. -/
private meta def openerText : Syntax → String
  | .node _ _ #[stx] => openerText stx
  | .atom _ v => v
  | _ => ""

/-- The position just after the next newline at or after `pos`. -/
private meta partial def afterNextLine (c : ParserContext) (pos : String.Pos.Raw) :
    Option String.Pos.Raw :=
  if c.atEnd pos then none
  else if c.get pos == '\n' then some (c.next pos)
  else afterNextLine c (c.next pos)

/-- The position of the first character at or after `pos` that is not a space. -/
private meta partial def afterSpaces (c : ParserContext) (pos : String.Pos.Raw) : String.Pos.Raw :=
  if !c.atEnd pos && c.get pos == ' ' then afterSpaces c (c.next pos) else pos

/-- The length of the run of colons that begins at `pos`. -/
private meta partial def colonRun (c : ParserContext) (pos : String.Pos.Raw) : Nat :=
  if !c.atEnd pos && c.get pos == ':' then colonRun c (c.next pos) + 1 else 0

/--
The end of a document's contents, which is `closePos` without the spaces and newlines that separate
them from the closing delimiter. They belong to the last block's token, as the whitespace before a
doc comment's closing delimiter does, so the contents end with their final character.
-/
private meta partial def contentEnd (c : ParserContext) (startPos closePos : String.Pos.Raw) :
    String.Pos.Raw :=
  if closePos.byteIdx ≤ startPos.byteIdx then closePos
  else
    let prev := c.prev closePos
    if c.get prev == ' ' || c.get prev == '\n' then contentEnd c startPos prev else closePos

/--
The start of the line that closes a document opened by `colons` colons, paired with the number of
colons that line begins with.

A line that begins with at least as many colons as the opener closes the document, so an author
keeps a delimiter out of a document's contents by opening it with a longer run.
-/
private meta partial def closingLine (colons : Nat) (c : ParserContext) (pos : String.Pos.Raw) :
    Option (String.Pos.Raw × Nat) :=
  -- The opening delimiter's trailing whitespace may already have reached the line after it, so the
  -- line `pos` is on counts when `pos` starts it.
  let here :=
    if pos.byteIdx == 0 || c.get (c.prev pos) == '\n' then
      let found := colonRun c (afterSpaces c pos)
      if found ≥ colons then some (pos, found) else none
    else none
  match here with
  | some found => some found
  | none =>
    match afterNextLine c pos with
    | none => none
    | some lineStart => closingLine colons c lineStart

/--
Parses a document that a run of colons closes.

The contents reach to the closing delimiter, which is found before they are read, so the document
ends where its input does and a stray character in it is reported where it occurs.
-/
public meta def document : Parser where
  fn := atomicFn fun c s =>
    let openerStx := s.stxStack.back
    let opener := openerText openerStx
    if opener.isEmpty || opener.any (· ≠ ':') then
      s.mkError s!"document opened by colons (got {opener.quote})"
    else
      let colons := opener.length
      match closingLine colons c s.pos with
      | none =>
        s.mkErrorAt s!"a line of {colons} colons to close the document"
          (openerStx.getHeadInfo.getPos!)
      | some (closePos, found) =>
        if found != colons then
          s.mkErrorAt s!"{colons} colons to close the document, not {found}" closePos
        else
          let contentsEnd := contentEnd c s.pos closePos
          let endPos :=
            if contentsEnd ≤ c.inputString.rawEndPos then contentsEnd else c.inputString.rawEndPos
          let s :=
            Verso.Parser.document (blockContext := {maxDirective := some (colons - 1)})
              (c.setEndPos endPos (by unfold endPos; split <;> simp [*])) s
          -- The contents stop at their last character, so the delimiter is where the parser resumes.
          if s.hasError then s else s.setPos (afterSpaces c closePos)

@[combinator_parenthesizer document] def document.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter document] def document.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

public meta def termDocument : Parser where
  fn := (atomicFn doc) >> whitespace
where
  doc : ParserFn := fun c s =>
    let opener := s.stxStack.back
    let indent := opener.getHeadInfo.getPos!

    let opener := openerText opener
    if opener.isEmpty || opener.any (· ≠ ':') || opener.length < 3 then
      s.mkError s!"document after at least three colons (got {opener.quote})"
    else
      -- The blocks start at or right of the colons' column, which a saved position enforces.
      let startPos := s.pos
      let blockContext := {maxDirective := some (opener.length - 1)}
      let s := adaptCacheableContextFn ({ · with savedPos? := indent })
        (ignoreFn Lean.Doc.Parser.lineTailWsFn >> blocksFn blockContext) c s
      if s.hasError then s
      else s.popSyntax.pushSyntax (Lean.Doc.Parser.setStartLeading startPos s.stxStack.back)

@[combinator_parenthesizer termDocument] def termDocument.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter termDocument] def termDocument.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

/-- Advance the parser to EOF on failure so Lean doesn't try to parse further commands -/
public meta def completeDocument : Parser where
  fn := (Lean.Parser.recoverFn Verso.Parser.document fun _ => skipFn) >> untilEoi
where
  untilEoi : ParserFn := fun c s =>
    s.setPos c.endPos

@[combinator_parenthesizer completeDocument] def completeDocument.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter completeDocument] def completeDocument.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

meta partial def findGenreTm : Syntax → TermElabM Unit
  | `($g:ident) => discard <| realizeGlobalConstNoOverloadWithInfo g -- Don't allow it to become an auto-argument
  | `(($e)) => findGenreTm e
  | _ => pure ()

meta partial def findGenreCmd (genre : Syntax) : Command.CommandElabM Unit :=
  Command.runTermElabM fun _ => findGenreTm genre

meta def saveRefs [Monad m] [MonadInfoTree m] (st : DocElabM.State) (st' : PartElabM.State) : m Unit := do
  for r in internalRefs st'.linkDefs st.linkRefs do
    for stx in r.syntax do
      pushInfoLeaf <| .ofCustomInfo {stx := stx , value := Dynamic.mk r}
  for r in internalRefs st'.footnoteDefs st.footnoteRefs do
    for stx in r.syntax do
      pushInfoLeaf <| .ofCustomInfo {stx := stx , value := Dynamic.mk r}


open PartElabM in
/--
All-at-once elaboration of verso document syntax to syntax denoting a verso `VersoDoc`. Implements
elaboration of the `#docs` command and `#doc` term. The `#doc` command is incremental, and thus
splits the logic in this function across multiple functions.
-/
private meta def elabDoc (genre: Term) (title: StrLit) (topLevelBlocks : Array Syntax) (endPos: String.Pos.Raw) : TermElabM Term := do
  let rootRangeStx ← getRef
  let env ← getEnv
  let titleParts ← stringToInlines title
  let titleString := inlinesToString env titleParts
  let ctx ← DocElabContext.fromGenreTerm genre
  let initDocState : DocElabM.State := { highlightDeduplicationTable := .some {} }
  -- Use the complete document syntax for the range, and the title syntax for the selection.
  -- This means that the outline contains all sub-parts, and clicking the root goes to the title.
  let initPartState : PartElabM.State := .init rootRangeStx title.raw

  let ((), docElabState, partElabState) ←
    PartElabM.run ctx initDocState initPartState <| do
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
  finished.toVersoDoc genre ctx docElabState partElabState

elab "#docs" "(" genre:term ")" n:ident title:str ":=" ":::::::" text:document ":::::::" : command => do
  findGenreCmd genre
  let rootRangeStx ← getRef
  let endTok :=
    match rootRangeStx with
    | .node _ _ t =>
      match t.back? with
      | some x => x
      | none => panic! "No final token!"
    | _ => panic! "Nothing"
  let endPos := endTok.getTailPos?.getD endTok.getPos!
  let doc ← Command.runTermElabM fun _ => elabDoc genre title text.raw.getArgs endPos
  Command.elabCommand (← `(def $n : VersoDoc $genre := $doc))

public syntax docTermBody :=
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
  let endPos := body.raw.getTailPos? |>.getD (← getFileMap).source.rawEndPos
  let docu ← elabDoc genre title body.raw[0][1].getArgs endPos
  Term.elabTerm (← ``( ($(docu) : VersoDoc $genre))) none


elab "#doc" "(" genre:term ")" title:str "=>" text:completeDocument eoi : term => do
  findGenreTm genre
  let endPos := (← getFileMap).source.rawEndPos
  let doc ← elabDoc genre title text.raw.getArgs endPos
  Term.elabTerm (← `( ($(doc) : VersoDoc $genre))) none

section
open Lean.Doc.Parser

-- `Lean.Doc.Parser.block` is an imported parser, so a formatter and parenthesizer cannot be
-- generated for it here. Verso never pretty-prints document syntax, so stubs suffice.
@[combinator_parenthesizer block]
def versoBlock.parenthesizer := PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter block]
def versoBlock.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

scoped syntax (name := addBlockCmd) block : command
scoped syntax (name := addLastBlockCmd) block : command
end

/-!
Unlike `#doc` expressions and `#docs` commands, which are elaborated all at once, `#doc` commands
are elaborated top-level-block by top-level-block in the manner of Lean's commands. This is done by
replacing the parser for the `command` category:
-/

/-- Replaces the stored parsing behavior for the category `cat` with the behavior defined by `p`. -/
private meta def replaceCategoryParser (cat : Name) (p : ParserFn) : Command.CommandElabM Unit :=
  modifyEnv (categoryParserFnExtension.modifyState · fun st =>
    fun n => if n == cat then p else st n)

/--
The ending position of the last Verso command that was successfully parsed.

The Lean command parser automatically skips whitespace and comments, but Lean comments can be Verso text, so we need to rewind and handle this ourself.
-/
meta initialize lastVersoEndPosExt : EnvExtension (Option String.Pos.Raw) ← registerEnvExtension (pure none)

/--
A version of `Lean.Syntax.updateTrailing` that converts `none` source info into `original` source info.

This is a bit of a hack. Verso's parser concocts tokens that don't exist in the source document in order
to make it easier to pattern match them with Lean quasiquotations, in a syntax that works in a Lean context.
These tokens have `none` source info, which `Lean.Syntax.updateTrailing` leaves untouched. Here, though, we need
them in order to communicate positions between command parses.
-/
private meta partial def updateSyntaxTrailing (trailing : Substring.Raw) : Syntax → Syntax
  | .atom info val => .atom (updateInfoTrailing trailing info) val
  | .ident info rawVal val pre => .ident (updateInfoTrailing trailing info) rawVal val pre
  | n@(.node info k args) =>
    if let some i := findIdxRev? (not ∘ empty) args then
     let last := updateSyntaxTrailing trailing args[i]
     let args := args.set i last;
     Syntax.node info k args
    else n
  | s => s
where
  findIdxRev? {α} (p : α → Bool) (xs : Array α) : Option (Fin xs.size) := do
    if h : xs.size = 0 then failure
    else
      let mut n : Fin xs.size := ⟨xs.size - 1, by grind⟩
      repeat
        if p xs[n] then return n
        if n.val = 0 then
          break
        else
          n := ⟨n.val - 1, by grind⟩
      failure

  empty : Syntax → Bool
  | .atom .. | .ident .. | .missing => false
  | .node .none _ args | .node (.synthetic ..) _ args => args.all empty
  | .node (.original leading _ trailing _) _ args =>
    leading.startPos == leading.stopPos && trailing.startPos == trailing.stopPos && args.all empty

  updateInfoTrailing (trailing : Substring.Raw) : SourceInfo → SourceInfo
    | .original leading pos _ endPos => .original leading pos trailing endPos
    | .none =>
      let pos := trailing.startPos
      .original {trailing with startPos := pos, stopPos := pos} pos trailing pos
    | info                                     => info


private meta partial def getTailContext? (source : String) (stx : Syntax) : Option (String.Pos.Raw × Substring.Raw) :=
  match stx with
  | .missing => none
  | .ident info .. | .atom info .. =>
    match info with
    | .none => none
    | .synthetic _ endPos _ => pure (endPos, ⟨source, endPos, endPos⟩)
    | .original _ _ trailing endPos => pure (endPos, trailing)
  | .node info _k args =>
    match info with
    | .none => args.findSomeRev? (getTailContext? source)
    | .synthetic _ endPos _ => pure (endPos, ⟨source, endPos, endPos⟩)
    | .original _ _ trailing endPos => pure (endPos, trailing)


/--
Parses each top-level block as either an `addBlockCmd` or an `addLastBlockCmd`. (This is what
Verso uses to replace the command parser.)
-/
private meta def versoBlockCommandFn : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let lastPos? := lastVersoEndPosExt.getState c.env
  let s := lastPos? |>.map s.setPos |>.getD s
  -- The block's final token takes the whitespace after it, so the next block starts at its own first
  -- token.
  let s := recoverBlockWith #[.missing] (blockFn { recordTrailing := true }) c s
  if s.hasError then s
  else
    let s := ignoreFn (manyFn blankLine) c s
    let s := updateTrailing c s
    let i := s.pos
    if c.atEnd i then
      s.mkNode ``addLastBlockCmd iniSz
    else
      s.mkNode ``addBlockCmd iniSz
where
  /--
  Updates the trailing whitespace information in the syntax at the top of the stack based on
  subsequently consumed whitespace.
  -/
  updateTrailing : ParserFn := fun c s =>
    let top := s.stxStack.back
    if let some ⟨_, tr⟩ := getTailContext? c.fileMap.source top then
      let tr := { tr with stopPos := s.pos }
      s.popSyntax.pushSyntax <| updateSyntaxTrailing tr top
    else
      s

/--
As we elaborate a `#doc` command top-level-block by top-level-block, the Lean environment will
be used to thread state between the separate top level blocks. These environment extensions contain
the state that needs to exist across top-level-block parsing events.
-/
public meta structure DocElabEnvironment where
  genreSyntax : Term := ⟨.missing⟩
  ctx : DocElabContext := ⟨.missing, mkConst ``Unit, .always, .none⟩
  docState : DocElabM.State := { highlightDeduplicationTable := some {} }
  partState : PartElabM.State := .init (.node .none nullKind #[]) (.node .none nullKind #[])
deriving Inhabited

public meta initialize docEnvironmentExt : EnvExtension DocElabEnvironment ← registerEnvExtension (pure {})

/--
The original parser for the `command` category, which is restored while elaborating a Verso block so
that nested Lean code has the correct syntax.
-/
meta initialize originalCatParserExt : EnvExtension CategoryParserFn ← registerEnvExtension (pure <| fun _ => whitespace)

/--
Performs `PartElabM.run` with state gathered from `docStateExt` and `partStateExt`, and then updates
the state in those environment extensions with any modifications. Also replaces the default command
parser in case `act` wants to parse commands (such as within an embedded code block).
-/
private meta def runPartElabInEnv (act : PartElabM a) : Command.CommandElabM a := do
  let env ← getEnv
  let versoCmdFn := categoryParserFnExtension.getState env
  let versoEnv := docEnvironmentExt.getState env

  try
    modifyEnv (fun env => categoryParserFnExtension.setState env <| originalCatParserExt.getState env)
    let (result, docState', partState') ← Command.runTermElabM fun _ => do
      PartElabM.run versoEnv.ctx versoEnv.docState versoEnv.partState act
    modifyEnv (docEnvironmentExt.setState · {versoEnv with docState := docState', partState := partState'})
    return result
  finally
    modifyEnv (categoryParserFnExtension.setState · versoCmdFn)

private meta def saveRefsInEnv : Command.CommandElabM Unit := do
  let versoEnv := docEnvironmentExt.getState (← getEnv)
  saveRefs versoEnv.docState versoEnv.partState

/-!
When we do incremental parsing of `#doc` commands, we split the behaviors that are done all at once
in `elabDoc` across three functions: the prelude in `startDoc`, the loop body in `runVersoBlock`,
and the postlude in `finishDoc`.
-/

private meta def startDoc (genreSyntax : Term) (title: StrLit) : Command.CommandElabM Unit := do
  let rootRangeStx ← getRef
  let env ← getEnv
  let titleParts ← stringToInlines title
  let titleString := inlinesToString env titleParts
  let ctx ← Command.runTermElabM fun _ => DocElabContext.fromGenreTerm genreSyntax
  let initDocState : DocElabM.State := { highlightDeduplicationTable := .some {} }
  -- See `elabDoc`: the current command anchors the root range; the title literal is the selection.
  let initPartState : PartElabM.State := .init rootRangeStx title.raw

  modifyEnv (docEnvironmentExt.setState · ⟨genreSyntax, ctx, initDocState, initPartState⟩)
  runPartElabInEnv <| do
    PartElabM.setTitle titleString (← titleParts.mapM (elabInline ⟨·⟩))

private meta def runVersoBlock (block : VersoBlock) : Command.CommandElabM Unit := do
  runPartElabInEnv <| partCommand block
  -- This calls pushInfoLeaf a quadratic number of times for a for a linear number of top-level
  -- verso blocks, which should be harmless but may be inefficient. It may be desirable to tag
  -- info leaves that have already been pushed to avoid pushing them again.
  saveRefsInEnv

open PartElabM in
private meta def finishDoc : Command.CommandElabM Unit:= do
  let endPos := (← getFileMap).source.rawEndPos
  runPartElabInEnv <| do closePartsUntil 0 endPos

  let versoEnv := docEnvironmentExt.getState (← getEnv)
  let finished := versoEnv.partState.partContext.toPartFrame.close endPos
  pushInfoLeaf <| .ofCustomInfo {stx := (← getRef), value := Dynamic.mk finished.toTOC}

  -- The `_root_` prefix ensures that the installed identifier will ignore any ambient namespaces
  let n := mkIdent (`_root_ ++ (← currentDocName))
  let doc ← Command.runTermElabM fun _ => finished.toVersoDoc versoEnv.genreSyntax versoEnv.ctx versoEnv.docState versoEnv.partState

  let ty ← ``(VersoDoc $versoEnv.genreSyntax)
  Command.elabCommand (← `(public def $n : $ty := $doc))

syntax (name := replaceDoc) "#doc " "(" term ") " str " =>" : command
elab_rules : command
  | `(command|#doc ( $genreSyntax:term ) $title:str =>%$tok) => open Lean Parser Elab Command in do
  startDoc genreSyntax title

  -- Sets up basic incremental evaluation of documents by replacing Lean's command-by-command parser
  -- with a top-level-block parser.
  modifyEnv fun env => originalCatParserExt.setState env (categoryParserFnExtension.getState env)
  replaceCategoryParser `command versoBlockCommandFn

  if let some stopPos := tok.getTailPos? then
    let txt ← getFileMap

    -- Edge case: if there's a Lean comment right after `#doc`, then the Lean command parser will skip
    -- it. We need to tell the Verso parser to start parsing at the first block's first token, after
    -- skipping blank lines and indentation only.
    let mut pos := txt.source.pos! stopPos
    while h : pos ≠ txt.source.endPos do
      if pos.get h == ' ' || pos.get h == '\n' then
        pos := pos.next h
      else break
    modifyEnv fun env => lastVersoEndPosExt.setState env (some pos.offset)

    -- Edge case: if there's no blocks after the =>, the replacement command parser won't get called,
    -- so we detect that case and call finishDoc.
    if stopPos.extract txt.source txt.source.rawEndPos |>.all Char.isWhitespace then
      finishDoc

open Command in
/--
Updates the saved Verso parser position to the end of `b`'s trailing whitespace.
-/
private meta def updatePos (b : VersoBlock) : CommandElabM Unit := do
  let endPos? :=
    if b.raw.isMissing then
      none
    else
      b.raw.getTrailingTailPos?
  modifyEnv fun env => lastVersoEndPosExt.setState env endPos?

@[command_elab addBlockCmd]
public meta def elabVersoBlock : Command.CommandElab
  | `(addBlockCmd| $b:block) => do
    updatePos b
    runVersoBlock b
  | _ => throwUnsupportedSyntax

@[command_elab addLastBlockCmd]
public meta def elabVersoLastBlock : Command.CommandElab
  | `(addLastBlockCmd| $b:block) => do
    updatePos b
    runVersoBlock b
    -- Finish up the document
    finishDoc
  | _ => throwUnsupportedSyntax
