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
import Verso.Hooks
import Verso.Instances
import Verso.Parser
import Verso.SyntaxUtils

namespace Verso.Doc.Concrete

open Lean Parser

open Verso Parser SyntaxUtils Doc Elab



def document : Parser where
  fn := atomicFn <| Verso.Parser.document (blockContext := {maxDirective := some 6})

@[combinator_parenthesizer document] def document.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter document] def document.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

/-- Advance the parser to EOF on failure so Lean doesn't try to parse further commands -/
def completeDocument : Parser where
  fn := (recoverFn Verso.Parser.document fun _ => skipFn) >> untilEoi
where
  untilEoi : ParserFn := fun c s =>
    s.setPos c.input.endPos

@[combinator_parenthesizer completeDocument] def completeDocument.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter completeDocument] def completeDocument.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous


open Lean.Elab Command in
partial def findGenreCmd : Syntax → Lean.Elab.Command.CommandElabM Unit
  | `($g:ident) => discard <| liftTermElabM <| realizeGlobalConstNoOverloadWithInfo g -- Don't allow it to become an auto-argument
  | `(($e)) => findGenreCmd e
  | _ => pure ()

open Lean.Elab Term in
partial def findGenreTm : Syntax → TermElabM Unit
  | `($g:ident) => discard <| realizeGlobalConstNoOverloadWithInfo g -- Don't allow it to become an auto-argument
  | `(($e)) => findGenreTm e
  | _ => pure ()


def saveRefs [Monad m] [MonadInfoTree m] (st : DocElabM.State) (st' : PartElabM.State) : m Unit := do
  for r in internalRefs st'.linkDefs st.linkRefs do
    for stx in r.syntax do
      pushInfoLeaf <| .ofCustomInfo {stx := stx , value := Dynamic.mk r}
  for r in internalRefs st'.footnoteDefs st.footnoteRefs do
    for stx in r.syntax do
      pushInfoLeaf <| .ofCustomInfo {stx := stx , value := Dynamic.mk r}

elab "#docs" "(" genre:term ")" n:ident title:str ":=" ":::::::" text:document ":::::::" : command => open Lean Elab Command PartElabM DocElabM in do
  findGenreCmd genre
  let endTok :=
    match ← getRef with
    | .node _ _ t =>
      match t.back? with
      | some x => x
      | none => panic! "No final token!"
    | _ => panic! "Nothing"
  let endPos := endTok.getPos!
  let .node _ _ blocks := text.raw
    | dbg_trace "nope {ppSyntax text.raw}" throwUnsupportedSyntax

  let titleParts ← stringToInlines title
  let titleString := inlinesToString (← getEnv) titleParts
  let g ← runTermElabM fun _ => Lean.Elab.Term.elabTerm genre (some (.const ``Doc.Genre []))

  let ((), st, st') ← liftTermElabM <| PartElabM.run genre g {} (.init (.node .none nullKind titleParts)) <| do
    setTitle titleString (← liftDocElabM <| titleParts.mapM (elabInline ⟨·⟩))
    for b in blocks do partCommand ⟨b⟩
    closePartsUntil 0 endPos
    pure ()
  let finished := st'.partContext.toPartFrame.close endPos
  pushInfoLeaf <| .ofCustomInfo {stx := (← getRef) , value := Dynamic.mk finished.toTOC}
  saveRefs st st'

  elabCommand (← `(def $n : Part $genre := $(← finished.toSyntax genre)))

  let mut docState := st
  for hook in (← documentFinishedHooks) do
    let ((), docState') ← runTermElabM fun _ => hook ⟨genre, g⟩ st' docState
    docState := docState'

elab "#doc" "(" genre:term ")" title:str "=>" text:completeDocument eoi : term => open Lean Elab Term PartElabM DocElabM in do
  findGenreTm genre
  let endPos := (← getFileMap).source.endPos
  let .node _ _ blocks := text.raw
    | dbg_trace "nope {ppSyntax text.raw}" throwUnsupportedSyntax
  let titleParts ← stringToInlines title
  let titleString := inlinesToString (← getEnv) titleParts
  let g ← elabTerm genre (some (.const ``Doc.Genre []))
  let g ← instantiateMVars g
  let ((), st, st') ← PartElabM.run genre g {} (.init (.node .none nullKind titleParts)) <| do
    let mut errors := #[]
    setTitle titleString (← liftDocElabM <| titleParts.mapM (elabInline ⟨·⟩))
    for b in blocks do
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
  elabTerm (← `( ($(← finished.toSyntax genre) : Part $genre))) none


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
    let (val, s') := f s
    setter s'
    pure val
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
  let s := (recoverBlockWith #[.missing] (Verso.Parser.block {})) c s
  let s := s.pushSyntax genre
  let s := ignoreFn (manyFn blankLine) c s
  let i := s.pos
  if c.input.atEnd i then
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
  try
    let finished := partState.partContext.toPartFrame.close endPos
    pushInfoLeaf <| .ofCustomInfo {stx := (← getRef) , value := Dynamic.mk finished.toTOC}
    saveRefs (docStateExt.getState (← getEnv)) partState
    let n ← currentDocName
    let docName := mkIdentFrom title n
    let titleString := title.getString
    let titleStr : TSyntax ``Lean.Parser.Command.docComment := quote titleString
    elabCommand (← `($titleStr:docComment def $docName : Part $genre := $(← finished.toSyntax' genre)))
  finally
    let mut docState := docStateExt.getState (← getEnv)
    let genreExpr ← runTermElabM fun _ => Term.elabTerm genre (some (.const ``Doc.Genre [])) >>= instantiateExprMVars
    for hook in (← documentFinishedHooks) do
      let ((), docState') ← runTermElabM fun _ => hook ⟨genre, genreExpr⟩ partState docState
      docState := docState'

syntax (name := replaceDoc) "#doc" "(" term ")" str "=>" : command

elab_rules :command
  | `(command|#doc ( $genre:term ) $title:str =>%$tok) => open Lean Parser Elab Command in do
  findGenreCmd genre
  let titleParts ← stringToInlines title
  let titleString := inlinesToString (← getEnv) titleParts
  let initState : PartElabM.State := .init (.node .none nullKind titleParts)

  let (titleInlines, docState) ← runTermElabM <| fun _ => do
    let g ← Term.elabTerm genre (some (.const ``Doc.Genre [])) >>= instantiateMVars
    titleParts.mapM (elabInline ⟨·⟩) |>.run genre g {} initState
  modifyEnv (docStateExt.setState · docState)

  let initState := { initState with
    partContext.expandedTitle := some (titleString, titleInlines)
  }
  modifyEnv (partStateExt.setState · (some initState))

  -- If there's no blocks after the =>, then the command parser never gets called, so it needs special-casing here
  if let some stopPos := tok.getTailPos? then
    let txt ← getFileMap
    if txt.source.extract stopPos txt.source.endPos |>.all (·.isWhitespace) then
      finishDoc genre title
      return

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
    let some partState := partStateExt.getState env
      | throwErrorAt block "State not initialized"

    let ((), docState', partState') ← runTermElabM fun _ => do
      let g ← Term.elabTerm genre (some (.const ``Doc.Genre [])) >>= instantiateMVars
      partCommand block |>.run genre g (docStateExt.getState env) partState
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

elab (name := completeDoc) "#old_doc" "(" genre:term ")" title:str "=>" text:completeDocument eoi : command => open Lean Elab Term Command PartElabM DocElabM in do
  findGenreCmd genre
  let endPos := (← getFileMap).source.endPos
  let .node _ _ blocks := text.raw
    | dbg_trace "nope {ppSyntax text.raw}" throwUnsupportedSyntax
  let titleParts ← stringToInlines title
  let titleString := inlinesToString (← getEnv) titleParts
  let g ← runTermElabM fun _ => Lean.Elab.Term.elabTerm genre (some (.const ``Doc.Genre []))
  let initState : PartElabM.State := .init (.node .none nullKind titleParts)
  withTraceNode `Elab.Verso (fun _ => pure m!"Document AST elab") <|
    incrementallyElabCommand blocks
      (initAct := do setTitle titleString (← liftDocElabM <| titleParts.mapM (elabInline ⟨·⟩)))
      (endAct := fun ⟨st, st', _⟩ => withTraceNode `Elab.Verso (fun _ => pure m!"Document def") do
        let st' := st'.closeAll endPos
        let finished := st'.partContext.toPartFrame.close endPos
        pushInfoLeaf <| .ofCustomInfo {stx := (← getRef) , value := Dynamic.mk finished.toTOC}
        saveRefs st st'
        let n ← currentDocName
        let docName := mkIdentFrom title n
        let titleStr : TSyntax ``Lean.Parser.Command.docComment := quote titleString
        elabCommand (← `($titleStr:docComment def $docName : Part $genre := $(← finished.toSyntax' genre)))
        let mut docState := st
        for hook in (← documentFinishedHooks) do
          let ((), docState') ← runTermElabM fun _ => hook ⟨genre, g⟩ st' docState
          docState := docState')

      -- The heartbeat count is reset for each top-level Verso block because they are analogous to Lean commands.
      (handleStep := fun block => do
        let heartbeats ← IO.getNumHeartbeats
        withTheReader Core.Context ({· with initHeartbeats := heartbeats}) (partCommand ⟨block⟩))
      (run := fun act => runTermElabM fun _ => Prod.fst <$> PartElabM.run genre g {} initState act)

/--
Make the single elaborator for some syntax kind become incremental

This is useful because `elab` doesn't create an accessible name for the generated elaborator. It's
possible to predict it and apply the attribute, but this seems fragile - better to look it up.
Placing the attribute before `elab` itself doesn't work because the attribute ends up on the
`syntax` declaration. Seperate elaborators don't work if the syntax rule in question ends with an
EOF - `elab` provides a representation of it (which can be checked via `isMissing` to see if the
parser went all the way), but that's not present in the parser's own syntax objects. Quoting `eoi`
doesn't  work because the parser wants to read to the end of the file.
-/
scoped elab "elab" &"incremental" kind:ident : command =>
  open Lean Elab Command Term in do
  let k ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo kind
  let elabs := commandElabAttribute.getEntries (← getEnv) k
  match elabs with
  | [] => throwErrorAt kind "No elaborators for '{k}'"
  | [x] =>
    let elabName := mkIdentFrom kind x.declName
    elabCommand (← `(attribute [incremental] $elabName))
  | _ => throwErrorAt kind "Multiple elaborators for '{k}'"

elab incremental completeDoc
