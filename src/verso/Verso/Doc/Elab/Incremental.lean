/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean

open Lean Language Elab Command

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

namespace Verso.Elab

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

/--
Describes the relationship between a DSL's incremental snapshot type, the DSL elaborator's own
internal state, and the state used by Lean's incremental elaboration framework.
-/
class IncrementalSnapshot (snapshot : outParam Type) (σ : outParam Type) where
  /--
  A task that will provide the next state on demand, if relevant. Incremental elaboration traverses
  the chain of next states until it finds one that can't be reused.
  -/
  getNext : snapshot → Option (SnapshotTask snapshot)
  /--
  The specific piece of syntax that gave rise to this incremental snapshot.
  -/
  getStx : snapshot → Syntax
  /--
  The incremental DSL elaboration state computed as a result of this snapshot.
  -/
  getIncrState : snapshot → Task σ
  /--
  The Lean elaboration framework's snapshot (needed to provide incremental diagnostics)
  -/
  toLeanSnapshot : snapshot → Language.Snapshot
  /--
  How should a snapshot be constructed? The parameters are:
    * The syntax giving rise to this specific snapshot
    * A Lean snapshot
    * A task that will compute the updated state from the syntax during incremental elaboration
    * The next snapshot in the chain, if one exists. The final DSL snapshot will have `none` here.
  -/
  mkSnap : Syntax → Language.Snapshot → Task σ → Option (SnapshotTask snapshot) → snapshot

open Lean Elab Command in
open IncrementalSnapshot in
/--
Elaborates a custom command incrementally. The command is expected to be an elaborator for a DSL
that requires its own state handling, but is elaborated (like Lean) from top to bottom.

The parameters are:

 * `snapshot` is the type used for the DSL's intermediate elaboration snapshots. The
   `IncrementalSnapshot` instance describes the relationship between this type, the DSL elaborator's
   own monadic state `σ`, and the elaboration process.

 * `σ` is the DSL elaborator's own monadic state. This may differ from the state used in most of the
   DSL elaborator's API, because it must capture the _full_ state of `m`. In particular, if `m` is a
   transformer of `TermElabM`, then `σ` must include `TermElabM`'s state along with the DSL
   elaboration state.

 * `m` is the DSL's elaboration monad. It must support many of Lean's own elaboration effects, so it
   will frequently be a transformed `TermElabM`. If so, its `MonadStateOf σ` instance must capture
   `TermElabM`'s state, e.g. via `saveState` and `TermState.restoreFull`.

 * `cmd` is the complete syntax of the command being elaborated. This is used only for displaying
   interactive feedback to the user, and it should be a piece of syntax whose range encompasses all
   the individual steps to be elaborated.

 * `steps` is the individual steps to incrementally elaborate. These should all be contained within
   `cmd`. They are saved in incremental snapshots and compared (with `Syntax.structRangeEq`) to
   determine whether the snapshot should be re-used or invalidated.

 * `initAct` contains any monadic actions to run to establish an initial elaboration state prior to
   elaborating the command steps.

 * `endAct` contains any monadic actions to run after incremental elaboration is completed.

 * `handleStep` describes the DSL's elaboration procedure for a single step from `steps`.

 * `lift` is a means of running the DSL's monad inside `CommandElabM`.

The caller is responsible for resolving the returned promise to indicate to Lean that the command is
fully elaborated. This should be the last thing it does after any further state changes.

Ordinary exceptions thrown by `handleStep` are caught and logged incrementally, unless they
represent unrecoverable internal Lean errors, in which case incremental elaboration is terminated.
-/
def incrementallyElabCommand
    [IncrementalSnapshot snapshot σ]
    [TypeName snapshot] [ToSnapshotTree snapshot] [Nonempty snapshot]
    [Nonempty σ]
    [Monad m] [MonadLiftT BaseIO m] [MonadExcept Exception m] [MonadLog m] [AddMessageContext m] [MonadFinally m]
    [MonadStateOf σ m]
    (cmd : Syntax)
    (steps : Array Syntax)
    (initAct : m Unit)
    (endAct : m Unit)
    (handleStep : Syntax → m Unit)
    (lift : {α : _} → m α → CommandElabM α)
    : CommandElabM (IO.Promise snapshot × σ) := do
  if let some snap := (← read).snap? then
    withReader (fun ρ => {ρ with snap? := none}) do
      lift <| do
        let mut oldSnap? := snap.old?.bind (·.val.get.toTyped? (α := snapshot))
        let mut nextPromise ← IO.Promise.new
        let initData := {diagnostics := .empty}
        snap.new.resolve <| DynamicSnapshot.ofTyped <|
          mkSnap cmd initData (.pure (← get)) (some {range? := cmd.getRange?, task := nextPromise.result})
        initAct
        let mut errors : MessageLog := .empty
        for b in steps do
          let mut reuseState := false
          if let some oldSnap := oldSnap? then
            if let some next := getNext oldSnap then
              -- if next.get.data.stx.structRangeEqWithTraceReuse (← getOptions) b then
              if next.get |> getStx |>.structRangeEq b then
                -- If they match, do nothing and advance the snapshot
                let σ := next.get |> getIncrState |>.get
                set σ
                errors := next.get |> toLeanSnapshot |>.diagnostics.msgLog
                oldSnap? := next.get
                reuseState := true
          let nextNextPromise ← IO.Promise.new
          let updatedState ← IO.Promise.new
          nextPromise.resolve <|
            mkSnap b {diagnostics := ⟨errors, none⟩} updatedState.result
              (some {range? := b.getRange?, task := nextNextPromise.result})

          try
            if not reuseState then
              oldSnap? := none
              try handleStep b
              catch e => errors := errors.add <| ← exnMessage e

            updatedState.resolve <| ← get
            nextPromise := nextNextPromise
          finally
            -- In case of a fatal exception in partCommand, we need to make sure that the promise actually
            -- gets resolved to avoid hanging forever. And the first resolve wins, so the second one is a
            -- no-op the rest of the time.
            nextPromise.resolve <| mkSnap b {diagnostics := ⟨errors, none⟩} (.pure (← get)) none
            updatedState.resolve <| ← get -- some old state goes here
        endAct
        pure (nextPromise, ← get)
  else -- incrementality not available - just do the action the easy way
    lift <| do
      initAct
      for b in steps do
        handleStep b
      endAct
      pure (← IO.Promise.new, ← get)
