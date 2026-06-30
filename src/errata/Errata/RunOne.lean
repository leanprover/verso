/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.Runner

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
The outcome of running a single test, in a form the infoview widget renders. The status is one of
{lit}`"passed"`, {lit}`"failed"`, {lit}`"error"`, or {lit}`"skipped"`.
-/
structure RunOutcome where
  /-- The overall verdict: {lit}`"passed"`, {lit}`"failed"`, {lit}`"error"`, or {lit}`"skipped"`. -/
  status : String
  /-- How long the run took, in milliseconds. -/
  durationMs : Nat
  /-- The failure or skip message, when the test did not pass. -/
  message? : Option String := none
  /-- Supporting detail for a failure, such as a diff or counterexample. -/
  detail? : Option String := none
  /-- The captured output, in order, with each chunk tagged by the stream it was written to. -/
  output : Array OutputChunk := #[]
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited

/-- The status name a single result contributes. -/
private def statusName : Status → String
  | .pass => "passed"
  | .fail _ => "failed"
  | .error _ => "error"
  | .skip _ => "skipped"

/-- The message a status carries, when it did not pass. -/
private def statusMessage : Status → Option String
  | .pass => none
  | .fail f => some f.message
  | .error m => some m
  | .skip r => some r

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
present (error over failed over skipped over passed), the message and detail come from the first
result with that status, and the output is every result's captured fragments in order, each tagged by
its stream.
-/
def summarizeResults (results : Array Result) : RunOutcome := Id.run do
  let rank : Status → Nat
    | .error _ => 3
    | .fail _ => 2
    | .skip _ => 1
    | .pass => 0
  let worst := results.foldl (fun acc r => if rank r.status > rank acc then r.status else acc) .pass
  let duration := results.foldl (fun acc r => acc + r.durationMs) 0
  let output := results.foldl (fun acc r => r.output.log.foldl pushFragment acc) #[]
  return {
    status := statusName worst
    durationMs := duration
    message? := statusMessage worst
    detail? := match worst with | .fail f => f.detail? | _ => none
    output
  }

/--
Runs one testable value to completion and condenses its results into a {name}`RunOutcome`. Captured
output is kept on a passing result too, since the widget shows it on demand rather than only on
failure.
-/
def runValue {α} [IsTest α] (location : Location) (value : α)
    (sink : Output → IO Unit := fun _ => pure ()) : IO RunOutcome := do
  let log ← IO.mkRef (#[] : Array Result)
  let usedOptions ← IO.mkRef ∅
  let cfg : Context := { log, usedOptions, location, writeOutput := sink }
  let start ← IO.monoMsNow
  let (outcome, output) ← runCapturing cfg (IsTest.toTest value)
  let dur := (← IO.monoMsNow) - start
  let logged ← log.get
  let results :=
    match outcome with
    | .error e => logged.push { cfg.error (toString e) dur with output }
    | .ok (.error f) => logged.push { cfg.fail f dur with output }
    | .ok (.ok ()) => if logged.isEmpty then #[{ cfg.pass dur with output }] else logged
  return summarizeResults results

/-- Runs one testable value with a default failure location, for callers without a source range. -/
def runValueDefault {α} [IsTest α] (value : α) : IO RunOutcome := runValue default value
