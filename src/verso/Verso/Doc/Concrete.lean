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

-- Note (DTC, 2024-04-18):
-- These are temporarily taken from PR #3636/#3940 and will need to be removed as incrementality becomes
-- part of Lean
namespace Lean
/--
Gets the end position information from a `SourceInfo`, if available.
If `originalOnly` is true, then `.synthetic` syntax will also return `none`.
-/
def SourceInfo.getTailPos? (info : SourceInfo) (canonicalOnly := false) : Option String.Pos :=
  match info, canonicalOnly with
  | original (endPos := endPos) ..,  _
  | synthetic (endPos := endPos) (canonical := true) .., _
  | synthetic (endPos := endPos) .., false => some endPos
  | _,                               _     => none

def SourceInfo.getRange? (canonicalOnly := false) (info : SourceInfo) : Option String.Range :=
  return ⟨(← info.getPos? canonicalOnly), (← info.getTailPos? canonicalOnly)⟩

namespace Syntax
/--
Compare syntax structures and position ranges, but not whitespace.
We generally assume that if syntax trees equal in this way generate the same elaboration output,
including positions contained in e.g. diagnostics and the info tree.
-/
partial def structRangeEq : Syntax → Syntax → Bool
  | .missing, .missing => true
  | .node info k args, .node info' k' args' =>
    info.getRange? == info'.getRange? && k == k' && args.isEqv args' structRangeEq
  | .atom info val, .atom info' val' => info.getRange? == info'.getRange? && val == val'
  | .ident info rawVal val preresolved, .ident info' rawVal' val' preresolved' =>
    info.getRange? == info'.getRange? && rawVal == rawVal' && val == val' &&
    preresolved == preresolved'
  | _, _ => false

/-- Like `structRangeEq` but prints trace on failure if `trace.Elab.reuse` is activated. -/
def structRangeEqWithTraceReuse (opts : Options) (stx1 stx2 : Syntax) : Bool :=
  if stx1.structRangeEq stx2 then
    true
  else
    if opts.getBool `trace.Elab.reuse then
      dbg_trace "reuse stopped: {stx1} != {stx2}"
      false
    else
      false
end Syntax
end Lean

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

private def exnMessage [Monad m] [MonadLog m] [AddMessageContext m] [MonadExcept Exception m] (exn : Exception) : m Message := do
  match exn with
  | .error ref msg =>
    let ref    := replaceRef ref (← MonadLog.getRef)
    let pos    := ref.getPos?.getD 0
    let endPos := ref.getTailPos?.getD pos
    let fileMap ← getFileMap
    let msgData ← addMessageContext msg
    pure { fileName := (← getFileName), pos := fileMap.toPosition pos, endPos := fileMap.toPosition endPos, data := msgData, severity := .error }
  | oops@(.internal _ _) => throw oops

open Lean Elab Command in
def incrementallyElabCommand
    [TypeName snapshot] [ToSnapshotTree snapshot] [Nonempty snapshot]
    [Nonempty σ]
    [Monad m] [MonadLiftT BaseIO m] [MonadExcept Exception m] [MonadLog m] [AddMessageContext m] [MonadFinally m]
    (cmd : Syntax)
    (steps : Array Syntax)
    (initAct : m Unit)
    (endAct : m Unit)
    (handleStep : Syntax → m Unit)
    (getState : m σ)
    (setState : σ → m Unit)
    (getNext : snapshot → Option (SnapshotTask snapshot))
    (getData : snapshot → snapshotData)
    (getStx : snapshotData → Syntax)
    (getIncrState : snapshotData → Task σ)
    (lift : {α : _} → m α → CommandElabM α)
    (mkData : Syntax → Language.Snapshot → Task σ → snapshotData)
    (dataSnap : snapshotData → Language.Snapshot)
    (mkSnap : snapshotData → Array (SnapshotTask snapshot) → snapshot)
    : CommandElabM (IO.Promise snapshot × σ) := do
  if let some snap := (← read).snap? then
    withReader (fun ρ => {ρ with snap? := none}) do
      lift <| do
        let mut oldSnap? := snap.old?.bind (·.val.get.toTyped? (α := snapshot))
        let mut nextPromise ← IO.Promise.new
        let initData := {diagnostics := .empty}
        snap.new.resolve <| DynamicSnapshot.ofTyped <|
          mkSnap (mkData cmd initData <| .pure (← getState))
            #[{range? := cmd.getRange?, task := nextPromise.result}]
        initAct
        let mut errors : MessageLog := .empty
        for b in steps do
          let mut reuseState := false
          if let some oldSnap := oldSnap? then
            if let some next := getNext oldSnap then
              -- if next.get.data.stx.structRangeEqWithTraceReuse (← getOptions) b then
              if next.get |> getData |> getStx |>.structRangeEq b then
                -- If they match, do nothing and advance the snapshot
                let σ := next.get |> getData |> getIncrState |>.get
                setState σ
                errors := next.get |> getData |> dataSnap |>.diagnostics.msgLog
                oldSnap? := next.get
                reuseState := true
          let nextNextPromise ← IO.Promise.new
          let updatedState ← IO.Promise.new
          nextPromise.resolve <| mkSnap (mkData b {diagnostics := ⟨errors, none⟩} updatedState.result)
            #[{range? := b.getRange?, task := nextNextPromise.result}]

          try
            if not reuseState then
              oldSnap? := none
              try handleStep b
              catch e => errors := errors.add <| ← exnMessage e

            updatedState.resolve <| ← getState
            nextPromise := nextNextPromise
          finally
            -- In case of a fatal exception in partCommand, we need to make sure that the promise actually
            -- gets resolved to avoid hanging forever. And the first resolve wins, so the second one is a
            -- no-op the rest of the time.
            nextPromise.resolve <| mkSnap (mkData b {diagnostics := ⟨errors, none⟩} (.pure (← getState))) #[]
            updatedState.resolve <| ← getState -- some old state goes here
        endAct
        pure (nextPromise, ← getState)
  else -- incrementality not available - just do the action the easy way
    lift <| do
      initAct
      for b in steps do
        handleStep b
      endAct
      pure (← IO.Promise.new, ← getState)

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
    let (nextPromise, snapshotState@⟨st, st', _⟩) ←
      incrementallyElabCommand text blocks
        (initAct := do setTitle titleString (← liftDocElabM <| titleParts.mapM elabInline))
        (endAct := closePartsUntil 0 endPos)
        (handleStep := partCommand)
        (getState := getSnapshotState)
        (setState := fun ⟨docState, partState, termState⟩ => do set docState; set partState; termState.restoreFull)
        (getNext := (·.next[0]?))
        (getData := (·.data))
        (getStx := (·.stx))
        (getIncrState := (·.finished))
        (lift := fun act => liftTermElabM <| Prod.fst <$> PartElabM.run {} initState act)
        (mkData := fun stx snap => DocElabSnapshotData.mk snap stx)
        (dataSnap := DocElabSnapshotData.toSnapshot)
        (mkSnap := DocElabSnapshot.mk)

    let finished := st'.partContext.toPartFrame.close endPos
    pushInfoLeaf <| .ofCustomInfo {stx := (← getRef) , value := Dynamic.mk finished.toTOC}
    saveRefs st st'
    let docName ← mkIdentFrom title <$> currentDocName
    elabCommand (← `(def $docName : Part $genre := $(← finished.toSyntax genre st'.linkDefs st'.footnoteDefs)))
    nextPromise.resolve <| DocElabSnapshot.mk {
      stx := text,
      finished := .pure snapshotState
      diagnostics := .empty
    } #[]
