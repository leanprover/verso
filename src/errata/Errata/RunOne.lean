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
  /--
  The identifier of the named result that wrote the chunk. {lean}`0` refers to the test itself,
  outside of any named result, while named results are assigned unique identifiers by the runner.
  -/
  result : Nat := 0
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq

/-- The chunk for a single captured output fragment, tagged by its stream. -/
def OutputChunk.ofOutput : Output → OutputChunk
  | .stdout s => { stream := "stdout", text := s }
  | .stderr s => { stream := "stderr", text := s }

/--
The verdict of one result, as the InfoView widget shows it: {name}`Errata.Status` without its
message and detail, which are separate fields of the result.
-/
inductive ResultNode.Status where
  /-- The result and everything below it passed. -/
  | passed
  /-- The result failed a check, or something below it did. -/
  | failed
  /-- An error escaped the result, so it reached no verdict of its own. -/
  | error
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq, BEq

/--
The source location of a failed check, with all information needed for an InfoView widget.
-/
structure ResultNode.Source where
  /-- The document that contains the check. -/
  uri : String
  /-- The line the check starts on, counted from zero. -/
  startLine : Nat
  /-- The column the check starts at, counted from zero. -/
  startColumn : Nat
  /-- The line the check ends on, counted from zero. -/
  endLine : Nat
  /-- The column the check ends at, counted from zero. -/
  endColumn : Nat
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq

/--
A source span, for an editor. Lean counts lines from one and the editor's protocol counts them from
zero.
-/
def ResultNode.Source.ofLocation (l : Location) : ResultNode.Source where
  uri := System.Uri.pathToUri l.file
  startLine := l.startPos.line - 1
  startColumn := l.startPos.column
  endLine := l.endPos.line - 1
  endColumn := l.endPos.column

/--
One result of a run, as the InfoView widget shows it: the test's own, identified by {lit}`0`, or a
named result below it. Its output and its duration cover only its own code. The output from and
durations of named results below it are attributed to these more specific results.
-/
structure ResultNode where
  /-- The result's identifier within its run. -/
  id : Nat
  /-- The result that contains this one. -/
  parent : Nat
  /-- The name the result was given; empty for the test's own. -/
  name : String
  /-- The verdict, once the result has one. Absent while it is still running. -/
  status? : Option ResultNode.Status := none
  /-- How long the result's own code took, in milliseconds. -/
  durationMs : Nat := 0
  /-- The failure or error message, when it did not pass. -/
  message? : Option String := none
  /-- Supporting detail for a failure, such as a diff or counterexample. -/
  detail? : Option String := none
  /-- Where the check that failed is, when it is known. -/
  location? : Option ResultNode.Source := none
  /-- What the result's own code wrote, in order, with each chunk tagged by its stream. -/
  output : Array OutputChunk := #[]
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited

/-- The identifier of the test's own result, which contains the named results of a run. -/
def ResultNode.root : Nat := 0

/-- The outcome of running a single test, in a form the InfoView widget renders. -/
structure RunOutcome where
  /-- The overall verdict, the most severe among the run's results. -/
  status : ResultNode.Status
  /-- How long the run took, in milliseconds. -/
  durationMs : Nat
  /-- The failure or error message, when the test did not pass. -/
  message? : Option String := none
  /-- Supporting detail for a failure, such as a diff or counterexample. -/
  detail? : Option String := none
  /-- Where the check that failed is, when it is known. -/
  location? : Option ResultNode.Source := none
  /--
  The run's results: the test's own, which leads, and one for each named result below it, each with
  the output its own code wrote. A result is followed by those recorded inside it.
  -/
  results : Array ResultNode := #[]
  /-- The test's docstring, rendered as Markdown, when it has one. -/
  description? : Option String := none
  /--
  The seed for property tests that the run used, so a failure can be run again with it. It is a
  string of decimal digits, which JavaScript reads exactly at any size. Absent when the test did not
  run at all.
  -/
  seed? : Option String := none
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited

/-- The test's own result, which contains the named results of the run. -/
def RunOutcome.root? (o : RunOutcome) : Option ResultNode :=
  o.results.find? (·.id == ResultNode.root)

/-- Everything the run wrote, its results in the order they ran. -/
def RunOutcome.allOutput (o : RunOutcome) : Array OutputChunk :=
  o.results.foldl (fun acc node => acc ++ node.output) #[]

/-- The verdict of a single result. -/
private def verdictOf : Status → ResultNode.Status
  | .pass => .passed
  | .fail _ => .failed
  | .error _ => .error

/-- The message a status carries, when it did not pass. -/
private def statusMessage : Status → Option String
  | .pass => none
  | .fail f => some f.message
  | .error m => some m

/-- Details about a failed test. -/
private def statusDetail : Status → Option String
  | .fail f => f.detail?
  | .pass | .error _ => none

private def statusLocation (testLocation : Location) : Status → Option ResultNode.Source
  | .fail f => do
    let l ← f.location?
    if l.file.isEmpty || l == testLocation then none else some (.ofLocation l)
  | .pass | .error _ => none

/-- Appends one output fragment, merging it into the previous chunk when it is from the same stream. -/
private def pushFragment (chunks : Array OutputChunk) (o : Output) : Array OutputChunk :=
  let stream := match o with | .stdout _ => "stdout" | .stderr _ => "stderr"
  match chunks.back? with
  | some last => if last.stream == stream
      then chunks.pop.push { last with text := last.text ++ o.text }
      else chunks.push { stream, text := o.text }
  | none => chunks.push { stream, text := o.text }

/--
The node for a finished result, with the given identifier and parent.
-/
def ResultNode.ofResult (id parent : Nat) (testLocation : Location) (r : Result) : ResultNode where
  id := id
  parent := parent
  name := r.resultPath.back?.getD ""
  status? := some (verdictOf r.status)
  durationMs := r.durationMs
  message? := statusMessage r.status
  detail? := statusDetail r.status
  location? := statusLocation testLocation r.status
  output := r.output.log.foldl pushFragment #[]

private def nodesOfResults (testLocation : Location) (results : Array Result) :
    Array ResultNode := Id.run do
  let mut nodes : Array ResultNode := #[]
  -- The identifier of the result open at each depth, innermost last.
  let mut enclosing : Array Nat := #[]
  for r in results do
    let up := enclosing.extract 0 r.resultPath.size
    let id := nodes.size
    nodes := nodes.push (.ofResult id (up.back?.getD ResultNode.root) testLocation r)
    enclosing := up.push id
  return nodes

/--
Condenses the results of one test run into a single outcome. The verdict is the most severe status
present (error over failed over passed). The message and detail come from the innermost result
with that status, since a test's own result reports a named result's failure only in summary while
the named result reports the actual assertion that failed. Each result becomes a node with its own
output. {name}`seed` is the seed for property tests, and {name}`testLocation` is the test's own
source range, which is used as a location of last resort.
-/
def summarizeResults (seed : Nat) (testLocation : Location) (results : Array Result) :
    RunOutcome := Id.run do
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
  return {
    status := verdictOf worst
    durationMs := duration
    message? := statusMessage worst
    detail? := statusDetail worst
    location? := statusLocation testLocation worst
    results := nodesOfResults testLocation results
    seed? := some (toString seed)
  }

/--
Runs one test action to completion and condenses its results into a {name}`RunOutcome`. Captured
output is kept on a passing result too, since the widget shows it on demand rather than only on
failure. Without a seed for property tests, one is drawn.
-/
def runAction (location : Location) (act : TestM Unit) (seed? : Option Nat := none)
    (sink : Output → IO Unit := fun _ => pure ())
    (watch : ResultEvent → IO Unit := fun _ => pure ()) : IO RunOutcome := do
  let cfg := {
    ← mkContext (seed := seed?) with location, writeOutput := sink, watchResults := watch
  }
  let start ← IO.monoMsNow
  let (outcome, output) ← runCapturing cfg act
  let dur := (← IO.monoMsNow) - start
  let logged ← cfg.log.get
  -- The test's own result leads the results it recorded, as the batch runner orders them.
  let own := cfg.resultOfOutcome outcome output dur (← cfg.insideMs.get) logged
  return summarizeResults cfg.seed cfg.location (#[own] ++ logged)

/-- Runs one testable value as {name}`runAction` does. -/
def runValue {α} [IsTest α] (location : Location) (value : α) (seed? : Option Nat := none)
    (sink : Output → IO Unit := fun _ => pure ())
    (watch : ResultEvent → IO Unit := fun _ => pure ()) : IO RunOutcome :=
  runAction location (IsTest.toTest value) seed? sink watch

/-- Runs one testable value with a default failure location, for callers without a source range. -/
def runValueDefault {α} [IsTest α] (value : α) : IO RunOutcome := runValue default value
