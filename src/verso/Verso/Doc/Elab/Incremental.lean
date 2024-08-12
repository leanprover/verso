/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.Command
import Lean.Elab.Term
import Lean.Language.Basic

open Lean Language Elab Command

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

namespace Internal
inductive IncrementalSnapshot where
  | mk
    (underlying : Language.Snapshot)
    (data : Dynamic)
    (next : Option (SnapshotTask IncrementalSnapshot))
    («syntax» : Syntax)
deriving TypeName, Nonempty

partial
instance : ToSnapshotTree IncrementalSnapshot where
  toSnapshotTree := go where
    go := fun
      | .mk s _ next _ => ⟨s, next.map (·.map (sync := true) go) |>.toArray⟩

/--
The Lean elaboration framework's snapshot (needed to provide incremental diagnostics)
-/
def IncrementalSnapshot.toLeanSnapshot : (snap : IncrementalSnapshot) → Language.Snapshot
  | .mk underlying _ _ _ => underlying

def IncrementalSnapshot.data [TypeName α] : IncrementalSnapshot → Option α
  | .mk _ data _ _ => data.get? α

def IncrementalSnapshot.typeName : IncrementalSnapshot → Name
  | .mk _ data _ _ => data.typeName

/--
A task that will provide the next state on demand, if relevant. Incremental elaboration traverses
the chain of next states until it finds one that can't be reused.
-/
def IncrementalSnapshot.next : (snap : IncrementalSnapshot) → Option (SnapshotTask IncrementalSnapshot)
  | .mk _ _ next _ => next

/--
The specific piece of syntax that gave rise to this incremental snapshot.
-/
def IncrementalSnapshot.syntax : (snap : IncrementalSnapshot) → Syntax
  | .mk _ _ _ stx => stx

end Internal
/--
Describes the relationship between a DSL's incremental snapshot type, the DSL elaborator's own
internal state, and the state used by Lean's incremental elaboration framework.
-/
class IncrementalSnapshot (snapshot : outParam Type) (σ : outParam Type) extends TypeName snapshot where
  /--
  The incremental DSL elaboration state computed as a result of this snapshot.
  -/
  getIncrState : snapshot → Task σ

  /--
  How should a snapshot be constructed? The parameter is a task that will compute the updated state
  during incremental elaboration.
  -/
  mkSnap : Task σ → snapshot

private def freshSnapshot (ownMessageLog := true) : CoreM Language.Snapshot := do
  if ownMessageLog then
    pure {diagnostics := ← Snapshot.Diagnostics.ofMessageLog (← Core.getAndEmptyMessageLog)}
  else
    pure {diagnostics := ← Snapshot.Diagnostics.ofMessageLog .empty}

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

 * `steps` is the individual steps to incrementally elaborate. These should all be contained within
   `cmd`. They are saved in incremental snapshots and compared (with `Syntax.structRangeEq`) to
   determine whether the snapshot should be re-used or invalidated.

 * `initAct` contains any monadic actions to run to establish an initial elaboration state prior to
   elaborating the command steps.

 * `endAct` contains any monadic actions to run after incremental elaboration is completed.

 * `handleStep` describes the DSL's elaboration procedure for a single step from `steps`.

 * `lift` is a means of running the DSL's monad inside `CommandElabM`.

The caller is responsible for invoking the returned `CommandElabM` action to indicate to Lean that
it is finished. This should be the last thing it does after any further state changes.

Ordinary exceptions thrown by `handleStep` are caught and logged incrementally, unless they
represent unrecoverable internal Lean errors, in which case incremental elaboration is terminated.
-/
def incrementallyElabCommand
    [IncrementalSnapshot snapshot σ]
    [TypeName snapshot] [Nonempty snapshot]
    [Nonempty σ]
    [Monad m] [MonadLiftT BaseIO m] [MonadLiftT CoreM m] [MonadExcept Exception m] [MonadLog m] [AddMessageContext m] [MonadFinally m] [MonadOptions m]
    [MonadStateOf σ m]
    (steps : Array Syntax)
    (initAct : m Unit)
    (endAct : m Unit)
    (handleStep : Syntax → m Unit)
    (lift : {α : _} → m α → CommandElabM α)
    : CommandElabM (CommandElabM Unit × σ) := do
  let cmd := mkNullNode steps
  if let some snap := (← read).snap? then
    withReader (fun ρ => {ρ with snap? := none}) do
      lift <| do
        let mut oldSnap? := snap.old?.bind (·.val.get.toTyped? (α := Internal.IncrementalSnapshot))
        let mut nextPromise ← IO.Promise.new

        let initData : Language.Snapshot ← freshSnapshot
        snap.new.resolve <| DynamicSnapshot.ofTyped <|
          Internal.IncrementalSnapshot.mk initData (.mk <| mkSnap (.pure (← get))) (some {range? := cmd.getRange?, task := nextPromise.result}) cmd
        initAct
        for b in steps do
          let mut reuseState := false
          if let some oldSnap := oldSnap? then
            if let some next := oldSnap.next then
              if next.get.syntax.structRangeEqWithTraceReuse (← getOptions) b then
              --if next.get.syntax |>.structRangeEq b then
                let some data := next.get.data (α := snapshot)
                  | logErrorAt next.get.syntax
                      m!"Internal error: failed to re-used incremental state. Expected '{TypeName.typeName snapshot}' but got a '{next.get.typeName}'"
                -- If they match, do nothing and advance the snapshot
                let σ := data |> getIncrState |>.get
                set σ
                oldSnap? := next.get
                reuseState := true
          let nextNextPromise ← IO.Promise.new
          let updatedState ← IO.Promise.new

          nextPromise.resolve <|
            .mk (← freshSnapshot) (.mk <| mkSnap updatedState.result)
              (some {range? := b.getRange?, task := nextNextPromise.result}) b

          try
            if not reuseState then
              oldSnap? := none
              try handleStep b
              catch e => logMessage <| ← exnMessage e

            updatedState.resolve <| ← get
            nextPromise := nextNextPromise
          finally
            -- In case of a fatal exception in partCommand, we need to make sure that the promise actually
            -- gets resolved to avoid hanging forever. And the first resolve wins, so the second one is a
            -- no-op the rest of the time.
            nextPromise.resolve <| .mk (← freshSnapshot (ownMessageLog := false)) (.mk <| mkSnap (.pure (← get))) none b
            updatedState.resolve <| ← get -- some old state goes here
        endAct

        let finalState ← get
        let allDone : CommandElabM Unit := do
          nextPromise.resolve <| .mk (← liftCoreM (freshSnapshot (ownMessageLog := false))) (.mk <| mkSnap (.pure finalState)) none cmd
        pure (allDone, finalState)
  else -- incrementality not available - just do the action the easy way
    lift <| do
      initAct
      for b in steps do
        handleStep b
      endAct
      pure (pure (), ← get)
