/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean

import Verso.Doc
import Verso.Doc.Elab
import Verso.Doc.Elab.Monad
import Verso.Doc.Lsp
import Verso.Parser
import Verso.SyntaxUtils

namespace Verso.Doc.Concrete

open Lean Parser

open Verso Parser SyntaxUtils Doc Elab

defmethod ParserFn.inStringLiteral (p : ParserFn) : ParserFn := fun c s =>
  let s' := strLitFn c s
  if s'.hasError then s'
  else
    let strLit : TSyntax `str := ⟨s'.stxStack.back⟩
    let afterQuote := s.next c.input s.pos
    let iniSz := afterQuote.stxStack.size
    let s'' := adaptUncacheableContextFn (replaceInputFrom s.pos strLit.getString) p c {afterQuote with pos := s.pos}
    if s''.hasError then s'' -- TODO update source locations for string decoding
    else
      let out := s''.stxStack.extract iniSz s''.stxStack.size
      let s'' := {s' with stxStack := s'.stxStack ++ out}
      s''.mkNode nullKind iniSz
where
  replaceInputFrom (p : String.Pos) new (c : ParserContextCore) := {c with input := c.input.extract 0 p ++ new }

def eosFn : ParserFn := fun c s =>
  let i := s.pos
  if c.input.atEnd i then s
  else s.mkError "end of string literal"


def inStrLit (p : ParserFn) : Parser where
  fn := p.inStringLiteral

@[combinator_parenthesizer inStrLit] def inStrLit.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter inStrLit] def inStrLit.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

def inlineStr := inStrLit <| textLine

elab "inlines!" s:inlineStr : term => open Lean Elab Term in
  match s.raw with
  | `<low| [~_ ~(.node _ _ out) ] > => do
    let (tms, _) ← DocElabM.run {} (.init (← `(foo))) <| out.mapM elabInline
    elabTerm (← `(term| #[ $[$tms],* ] )) none
  | _ => throwUnsupportedSyntax

set_option pp.rawOnError true

/--
info: #[Inline.text "Hello, ", Inline.emph #[Inline.bold #[Inline.text "emph"]]] : Array (Inline Genre.none)
-/
#guard_msgs in
#check (inlines!"Hello, _*emph*_" : Array (Inline .none))

def document : Parser where
  fn := rawFn <| atomicFn <| Verso.Parser.document (blockContext := {maxDirective := some 6})

@[combinator_parenthesizer document] def document.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter document] def document.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

/-- Advance the parser to EOF on failure so Lean doesn't try to parse further commands -/
def completeDocument : Parser where
  fn := rawFn <| atomicFn <| recoverFn Verso.Parser.document untilEoi
where
  untilEoi : RecoveryContext → ParserFn := fun _ c s =>
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

elab "#docs" "(" genre:term ")" n:ident title:inlineStr ":=" ":::::::" text:document ":::::::" : command => open Lean Elab Command PartElabM DocElabM in do
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
  let ⟨`<low| [~_ ~(titleName@(.node _ _ titleParts))]>⟩ := title
    | dbg_trace "nope {ppSyntax title}" throwUnsupportedSyntax
  let titleString := inlinesToString (← getEnv) titleParts
  let ((), st, st') ← liftTermElabM <| PartElabM.run {} (.init titleName) <| do
    setTitle titleString (← liftDocElabM <| titleParts.mapM elabInline)
    for b in blocks do partCommand b
    closePartsUntil 0 endPos
    pure ()
  let finished := st'.partContext.toPartFrame.close endPos
  pushInfoLeaf <| .ofCustomInfo {stx := (← getRef) , value := Dynamic.mk finished.toTOC}
  saveRefs st st'

  elabCommand (← `(def $n : Part $genre := $(← finished.toSyntax genre st'.linkDefs st'.footnoteDefs)))


elab "#doc" "(" genre:term ")" title:inlineStr "=>" text:completeDocument eof:eoi : term => open Lean Elab Term PartElabM DocElabM in do
  findGenreTm genre
  let endPos := eof.raw.getTailPos?.get!
  let .node _ _ blocks := text.raw
    | dbg_trace "nope {ppSyntax text.raw}" throwUnsupportedSyntax
  let ⟨`<low| [~_ ~(titleName@(.node _ _ titleParts))]>⟩ := title
    | dbg_trace "nope {ppSyntax title}" throwUnsupportedSyntax
  let titleString := inlinesToString (← getEnv) titleParts
  let ((), st, st') ← PartElabM.run {} (.init titleName) <| do
    let mut errors := #[]
    setTitle titleString (← liftDocElabM <| titleParts.mapM elabInline)
    for b in blocks do
      try
        partCommand b
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
  elabTerm (← `( ($(← finished.toSyntax genre st'.linkDefs st'.footnoteDefs) : Part $genre))) none


macro "%doc" moduleName:ident : term =>
  pure <| mkIdentFrom moduleName <| docName moduleName.getId

macro "%docName" moduleName:ident : term =>
  let n := mkIdentFrom moduleName (docName moduleName.getId) |>.getId
  pure <| quote n


def currentDocName [Monad m] [MonadEnv m] : m Name := do
  pure <| docName <| (← Lean.MonadEnv.getEnv).mainModule

open Language

structure DocElabSnapshotState where
  docState : DocElabM.State
  partState : PartElabM.State
  termState : Term.SavedState
deriving Nonempty

open Lean Elab Term
private def getSnapshotState : PartElabM DocElabSnapshotState := do
  pure ⟨← getThe _, ← getThe _,  ← saveState (m := TermElabM)⟩

structure DocElabSnapshotData extends Language.Snapshot where
  stx      : Syntax
  finished : Task DocElabSnapshotState
deriving Nonempty

inductive DocElabSnapshot where
  | mk (data : DocElabSnapshotData) (next : Array (SnapshotTask DocElabSnapshot))
deriving TypeName, Nonempty

partial instance : ToSnapshotTree DocElabSnapshot where
  toSnapshotTree := go where
    go := fun ⟨s, next⟩ => ⟨s.toSnapshot, next.map (·.map (sync := true) go)⟩


abbrev DocElabSnapshot.data : DocElabSnapshot → DocElabSnapshotData
  | .mk data _ => data

abbrev DocElabSnapshot.next : DocElabSnapshot → Array (SnapshotTask DocElabSnapshot)
  | .mk _ next => next

private def exnMessage (exn : Exception) : TermElabM Message := do
  match exn with
  | .error ref msg =>
    let ref    := replaceRef ref (← MonadLog.getRef)
    let pos    := ref.getPos?.getD 0
    let endPos := ref.getTailPos?.getD pos
    let fileMap ← getFileMap
    let msgData ← addMessageContext msg
    pure { fileName := (← getFileName), pos := fileMap.toPosition pos, endPos := fileMap.toPosition endPos, data := msgData, severity := .error }
  | oops@(.internal _ _) => throw oops

elab "#doc" "(" genre:term ")" title:inlineStr "=>" text:completeDocument eof:eoi : command => open Lean Elab Term Command PartElabM DocElabM in do
  findGenreCmd genre
  if eof.raw.isMissing then
    throwError "Syntax error prevents processing document"
  else
    let endPos := eof.raw.getTailPos?.get!
    let .node _ _ blocks := text.raw
      | dbg_trace "nope {ppSyntax text.raw}" throwUnsupportedSyntax
    let ⟨`<low| [~_ ~(titleName@(.node _ _ titleParts))]>⟩ := title
      | dbg_trace "nope {ppSyntax title}" throwUnsupportedSyntax
    let titleString := inlinesToString (← getEnv) titleParts
    let initState : PartElabM.State := .init titleName
    let ctxt ← read
    let some snap := ctxt.snap?
      | throwErrorAt title "nope dawg"
    withReader (fun ρ => {ρ with snap? := none}) do
      let ((nextPromise, snapshotState), st, st') ← liftTermElabM <| PartElabM.run {} initState <| do
        let mut oldSnap? := snap.old?.bind (·.get.toTyped? (α := DocElabSnapshot))

        let mut nextPromise ← IO.Promise.new
        snap.new.resolve <| DynamicSnapshot.ofTyped <| DocElabSnapshot.mk {
            stx := ← `("I like to eat apples and bananas"),
            finished := .pure <| ← getSnapshotState,
            diagnostics := .empty
          } #[{range? := text.raw.getRange?, task := nextPromise.result}]

        setTitle titleString (← liftDocElabM <| titleParts.mapM elabInline)
        let mut errors : MessageLog := .empty
        for b in blocks do
          let mut reuseState := false
          if let some oldSnap := oldSnap? then
            if let some next := oldSnap.next[0]? then
              if next.get.data.stx.structRangeEqWithTraceReuse (← getOptions) b then
                -- If they match, do nothing and advance the snapshot
                let ⟨docState, partState, termState⟩ := next.get.data.finished.get
                set docState
                set partState
                termState.restoreFull
                errors := next.get.data.diagnostics.msgLog
                oldSnap? := next.get
                reuseState := true
          let nextNextPromise ← IO.Promise.new
          let updatedState ← IO.Promise.new
          nextPromise.resolve <| DocElabSnapshot.mk {
              stx := b,
              finished := updatedState.result,
              diagnostics := ⟨errors, none⟩
            } #[{range? := b.getRange?, task := nextNextPromise.result}]

          try
            if not reuseState then
              oldSnap? := none
              try partCommand b
              catch e => errors := errors.add <| ← exnMessage e

            updatedState.resolve <| ← getSnapshotState
            nextPromise := nextNextPromise
          finally
            -- In case of a fatal exception in partCommand, we need to make sure that the promise actually
            -- gets resolved to avoid hanging forever. And the first resolve wins, so the second one is a
            -- no-op the rest of the time.
            nextPromise.resolve <| DocElabSnapshot.mk {
                stx := b,
                finished := .pure <| ← getSnapshotState,
                diagnostics := ⟨errors, none⟩
              } #[]
            updatedState.resolve <| ← getSnapshotState -- some old state goes here

        closePartsUntil 0 endPos

        pure (nextPromise, ← getSnapshotState)
      let finished := st'.partContext.toPartFrame.close endPos
      pushInfoLeaf <| .ofCustomInfo {stx := (← getRef) , value := Dynamic.mk finished.toTOC}
      saveRefs st st'
      let docName ← mkIdentFrom title <$> currentDocName
      elabCommand (← `(def $docName : Part $genre := $(← finished.toSyntax genre st'.linkDefs st'.footnoteDefs)))
      nextPromise.resolve <| DocElabSnapshot.mk {
        stx := ← `(55.8),
        finished := .pure snapshotState
        diagnostics := .empty
      } #[]
