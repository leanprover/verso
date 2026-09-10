/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.IsTest
public import Errata.Runner
public import Lean.Data.Json

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/-- A run of captured output from a single stream, used to render output with the streams distinct. -/
structure OutputChunk where
  /-- The stream the text was written to: {lit}`"stdout"` or {lit}`"stderr"`. -/
  stream : String
  /-- The text written to that stream. -/
  text : String
  /-- When the chunk was received, in milliseconds since the Unix epoch; set by the runner. -/
  time : Nat := 0
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq

/-- The chunk for a single captured output fragment, tagged by its stream. -/
def OutputChunk.ofOutput : Output → OutputChunk
  | .stdout s => { stream := "stdout", text := s }
  | .stderr s => { stream := "stderr", text := s }

/--
The outcome of running a single test, in a form the InfoView widget renders. The status is one of
{lit}`"passed"`, {lit}`"failed"`, or {lit}`"error"`.
-/
structure RunOutcome where
  /-- The overall verdict: {lit}`"passed"`, {lit}`"failed"`, or {lit}`"error"`. -/
  status : String
  /-- How long the run took, in milliseconds. -/
  durationMs : Nat
  /-- The failure or error message, when the test did not pass. -/
  message? : Option String := none
  /-- Supporting detail for a failure, such as a diff or counterexample. -/
  detail? : Option String := none
  /-- The captured output, in order, with each chunk tagged by the stream it was written to. -/
  output : Array OutputChunk := #[]
  /-- The test's docstring, rendered as Markdown, when it has one. -/
  description? : Option String := none
  /--
  The seed for property tests that the run used, in decimal digits, so a failure can be run again
  with it. A string carries every natural number exactly through JavaScript's JSON. Absent when the
  test did not run at all.
  -/
  seed? : Option String := none
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited

/-- The status name a single result contributes. -/
private def statusName : Status → String
  | .pass => "passed"
  | .fail _ => "failed"
  | .error _ => "error"

/-- The message a status carries, when it did not pass. -/
private def statusMessage : Status → Option String
  | .pass => none
  | .fail f => some f.message
  | .error m => some m

/-- Appends one output fragment, merging it into the previous chunk when it is from the same stream. -/
private def pushFragment (chunks : Array OutputChunk) (o : Output) : Array OutputChunk :=
  let stream := match o with | .stdout _ => "stdout" | .stderr _ => "stderr"
  match chunks.back? with
  | some last => if last.stream == stream
      then chunks.pop.push { last with text := last.text ++ o.text }
      else chunks.push { stream, text := o.text }
  | none => chunks.push { stream, text := o.text }

/--
Condenses the results of one test run into a single outcome. The verdict is the most severe status
present (error over failed over passed). The message and detail come from the innermost result
with that status, since a test's own result reports a named result's failure only in summary while
the named result reports the assertion itself. The output is every result's captured fragments in
order, each tagged by its stream. {name}`seed` is the seed for property tests that the run used.
-/
def summarizeResults (seed : Nat) (results : Array Result) : RunOutcome := Id.run do
  let rank : Status → Nat
    | .error _ => 2
    | .fail _ => 1
    | .pass => 0
  let worstRank := results.foldl (fun acc r => max acc (rank r.status)) 0
  -- Among the results with the worst status, the innermost one has the concrete message.
  let innermost := results.foldl (init := none) fun (best : Option Result) r =>
    if rank r.status != worstRank then best
    else match best with
      | some b => if r.resultPath.size > b.resultPath.size then some r else best
      | none => some r
  let worst := (innermost.map (·.status)).getD .pass
  let duration := results.foldl (fun acc r => acc + r.durationMs) 0
  let output := results.foldl (fun acc r => r.output.log.foldl pushFragment acc) #[]
  return {
    status := statusName worst
    durationMs := duration
    message? := statusMessage worst
    detail? := match worst with | .fail f => f.detail? | _ => none
    output
    seed? := some (toString seed)
  }

/--
Runs one test action to completion and condenses its results into a {name}`RunOutcome`. Captured
output is kept on a passing result too, since the widget shows it on demand rather than only on
failure. Without a seed for property tests, one is drawn.
-/
def runAction (location : Location) (act : TestM Unit) (seed? : Option Nat := none)
    (sink : Output → IO Unit := fun _ => pure ()) : IO RunOutcome := do
  let cfg := { ← mkContext (seed := seed?) with location, writeOutput := sink }
  let start ← IO.monoMsNow
  let (outcome, output) ← runCapturing cfg act
  let dur := (← IO.monoMsNow) - start
  let logged ← cfg.log.get
  -- The test's own result leads the results it recorded, as the batch runner orders them.
  let own := cfg.resultOfOutcome outcome output dur (← cfg.insideMs.get) logged
  return summarizeResults cfg.seed (#[own] ++ logged)

/-- Runs one testable value as {name}`runAction` does. -/
def runValue {α} [IsTest α] (location : Location) (value : α) (seed? : Option Nat := none)
    (sink : Output → IO Unit := fun _ => pure ()) : IO RunOutcome :=
  runAction location (IsTest.toTest value) seed? sink

/-- Runs one testable value with a default failure location, for callers without a source range. -/
def runValueDefault {α} [IsTest α] (value : α) : IO RunOutcome := runValue default value
