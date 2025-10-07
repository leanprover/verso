/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc
import Verso.Doc.Concrete.InlineString
import Verso.Doc.Elab
import Verso.Doc.Elab.Incremental
import Verso.Doc.Elab.Monad
import Verso.Doc.Lsp
import Verso.Instances
import Verso.SyntaxUtils
import Verso.Parser

namespace Verso.Doc.Concrete

open Lean Doc

open Verso Parser SyntaxUtils Doc Elab


def document : Parser where
  fn := atomicFn <| Verso.Parser.document (blockContext := {maxDirective := some 6})

@[combinator_parenthesizer document] def document.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter document] def document.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

/-- Advance the parser to EOF on failure so Lean doesn't try to parse further commands -/
def completeDocument : Parser where
  fn := (Lean.Parser.recoverFn Verso.Parser.document fun _ => skipFn) >> untilEoi
where
  untilEoi : ParserFn := fun c s =>
    s.setPos c.endPos

@[combinator_parenthesizer completeDocument] def completeDocument.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter completeDocument] def completeDocument.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

open Lean.Elab Term in
partial def findGenreTm : Syntax → TermElabM Unit
  | `($g:ident) => discard <| realizeGlobalConstNoOverloadWithInfo g -- Don't allow it to become an auto-argument
  | `(($e)) => findGenreTm e
  | _ => pure ()

partial def findGenreCmd (genre : Syntax) : Command.CommandElabM Unit :=
  Command.liftTermElabM do findGenreTm genre

def saveRefs [Monad m] [MonadInfoTree m] (st : DocElabM.State) (st' : PartElabM.State) : m Unit := do
  for r in internalRefs st'.linkDefs st.linkRefs do
    for stx in r.syntax do
      pushInfoLeaf <| .ofCustomInfo {stx := stx , value := Dynamic.mk r}
  for r in internalRefs st'.footnoteDefs st.footnoteRefs do
    for stx in r.syntax do
      pushInfoLeaf <| .ofCustomInfo {stx := stx , value := Dynamic.mk r}

def elabGenre (genre : TSyntax `term) : TermElabM Expr :=
  Term.elabTerm genre (some (.const ``Doc.Genre []))

def elabDoc (genre: Term) (title: StrLit) (topLevelBlocks : Array Syntax) (endPos: String.Pos): TermElabM Term := do
  let titleParts ← stringToInlines title
  let titleString := inlinesToString (← getEnv) titleParts
  let initState : PartElabM.State := .init (.node .none nullKind titleParts)

  let ((), st, st') ← PartElabM.run genre (← elabGenre genre) {} initState <| do
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
  let finished := st'.partContext.toPartFrame.close endPos

  pushInfoLeaf <| .ofCustomInfo {stx := (← getRef) , value := Dynamic.mk finished.toTOC}
  saveRefs st st'
  finished.toSyntax genre

elab "#docs" "(" genre:term ")" n:ident title:str ":=" ":::::::" text:document ":::::::" : command => open Lean Elab Command PartElabM DocElabM in do
  findGenreCmd genre
  let endTok :=
    match ← getRef with
    | .node _ _ t =>
      match t.back? with
      | some x => x
      | none => panic! "No final token!"
    | _ => panic! "Nothing"
  let document ← runTermElabM fun _ => elabDoc genre title text.raw.getArgs endTok.getPos!
  elabCommand (← `(def $n : Part $genre := $(document)))

elab "#doc" "(" genre:term ")" title:str "=>" text:completeDocument eoi : term => open Lean Elab Term PartElabM DocElabM in do
  findGenreTm genre
  let endPos := (← getFileMap).source.endPos
  let document ← elabDoc genre title text.raw.getArgs endPos
  elabTerm (← `( ($(document) : Part $genre))) none


open Language

/--
The complete state of `PartElabM`, suitable for saving and restoration during incremental
elaboration
-/
structure DocElabSnapshotState where
  docState : DocElabM.State
  partState : PartElabM.State
  termState : Term.SavedState
deriving Nonempty

structure DocElabSnapshot where
  finished : Task (Option DocElabSnapshotState)
deriving Nonempty, TypeName

instance : IncrementalSnapshot DocElabSnapshot DocElabSnapshotState where
  getIncrState snap := snap.finished
  mkSnap := DocElabSnapshot.mk

instance : MonadStateOf DocElabSnapshotState PartElabM where
  get := getter
  set := setter
  -- Not great for linearity, but incrementality breaks that anyway and that's the only use case for
  -- this instance.
  modifyGet f := do
    let s ← getter
    let v := f s
    setter v.2
    pure v.1
where
  getter := do pure ⟨← getThe _, ← getThe _,  ← saveState (m := TermElabM)⟩
  setter
    | ⟨docState, partState, termState⟩ => do
      set docState
      set partState
      -- SavedState.restore doesn't  restore enough state, so dig in!
      set termState.elab
      (show MetaM Unit from set termState.meta.meta)
      (show CoreM Unit from set termState.meta.core.toState)

private def ifCat (cat : Name) (p : ParserFn) (fallback : Name → ParserFn) (n : Name) : ParserFn :=
  if n == cat then p else fallback n

open Lean Parser in
def replaceCategoryFn (cat : Name) (p : ParserFn) (env : Environment) : Environment :=
  categoryParserFnExtension.modifyState env fun st => ifCat cat p st

scoped syntax (name := addBlockCmd) block term:max : command
scoped syntax (name := addLastBlockCmd) block term:max str : command

def versoBlockCommandFn (genre : Term) (title : String) : ParserFn := fun c s =>
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

initialize docStateExt : EnvExtension DocElabM.State ← registerEnvExtension (pure {})
initialize partStateExt : EnvExtension (Option PartElabM.State) ← registerEnvExtension (pure none)
initialize originalCatParserExt : EnvExtension CategoryParserFn ← registerEnvExtension (pure <| fun _ => whitespace)

open Lean Elab Command in
def finishDoc (genre : Term) (title : StrLit) : CommandElabM Unit:= do
  -- Finish up the document
  let txt ← getFileMap
  let endPos := txt.source.endPos
  let some partState ← partStateExt.getState <$> getEnv
    | throwError "Document state not initialized"
  let partState := partState.closeAll endPos
  let finished := partState.partContext.toPartFrame.close endPos
  pushInfoLeaf <| .ofCustomInfo {stx := (← getRef) , value := Dynamic.mk finished.toTOC}
  saveRefs (docStateExt.getState (← getEnv)) partState
  let n ← currentDocName
  let docName := mkIdentFrom title n
  let titleString := title.getString
  let titleStr : TSyntax ``Lean.Parser.Command.docComment := quote titleString
  elabCommand (← `($titleStr:docComment def $docName : Part $genre := $(← finished.toSyntax' genre)))

syntax (name := replaceDoc) "#doc" "(" term ")" str "=>" : command

#check Lean.Doc.Syntax.blockquote

elab_rules : command
  | `(command|#doc ( $genre:term ) $title:str =>%$tok) => open Lean Parser Elab Command PartElabM in do
  findGenreCmd genre
  elabCommand <| ← `(open scoped Lean.Doc.Syntax)

  let titleParts ← stringToInlines title
  let titleString := inlinesToString (← getEnv) titleParts
  let initState : PartElabM.State := .init (.node .none nullKind titleParts)

  let ((), st, st') ← liftTermElabM <| PartElabM.run genre (← Command.runTermElabM fun _ => elabGenre genre) {} initState <| do
    setTitle titleString (← liftDocElabM <| titleParts.mapM (Verso.Doc.Elab.elabInline ⟨·⟩))
  modifyEnv (docStateExt.setState · st)
  modifyEnv (partStateExt.setState · (some st'))

  -- If there's no blocks after the =>, then the command parser never gets called, so it needs special-casing here
  if let some stopPos := tok.getTailPos? then
    let txt ← getFileMap
    if txt.source.extract stopPos txt.source.endPos |>.all (·.isWhitespace) then
      finishDoc genre title
      return

  -- This is messing with Lean's internal command parser to start
  -- treating blocks with the infrastructure for Lean commands
  -- The result of parsing a verso block is a lean command that will add this block to the
  -- current document
  modifyEnv fun env => originalCatParserExt.setState env (categoryParserFnExtension.getState env)
  modifyEnv (replaceCategoryFn `command (versoBlockCommandFn genre titleString))

open Lean Elab Command in
def runVersoBlock (genre : Term) (block : TSyntax `block) : CommandElabM Unit := withRef block do
  -- The original command parser must be restored here in case one of the Verso blocks is parsing
  -- Lean code during its elaboration.
  let versoCmdFn := (categoryParserFnExtension.getState (← getEnv))
  try
    modifyEnv fun env => categoryParserFnExtension.setState env (originalCatParserExt.getState env)
    let env ← getEnv
    -- This is where we keep the part
    let some partState := partStateExt.getState env
      | throwErrorAt block "State not initialized"

    let ((), docState', partState') ← runTermElabM fun _ => do
      let g ← Term.elabTerm genre (some (.const ``Doc.Genre [])) >>= instantiateMVars
      -- compare to line 79
      partCommand block |>.run genre g (docStateExt.getState env) partState
    saveRefs docState' partState'
    modifyEnv fun env =>
      partStateExt.setState (docStateExt.setState env docState') (some partState')
  finally
    modifyEnv (categoryParserFnExtension.setState · versoCmdFn)


open Lean Elab Command in
@[command_elab addBlockCmd]
def elabVersoBlock : CommandElab
  | `(addBlockCmd| $b:block $genre:term) => do
    runVersoBlock genre b
  | _ => throwUnsupportedSyntax

open Lean Elab Command in
@[command_elab addLastBlockCmd]
def elabVersoLastBlock : CommandElab
  | `(addLastBlockCmd| $b:block $genre:term $title:str) => do
    runVersoBlock genre b
    -- Finish up the document
    finishDoc genre title
  | _ => throwUnsupportedSyntax
