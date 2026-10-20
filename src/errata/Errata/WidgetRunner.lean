/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module

public import Errata.WidgetOutcome
public import Errata.IsTest
public import Errata.Runner

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata.Widget.Runner

/-- The verdict of a single result. -/
private def verdictOf : Status → ResultNode.Status
  | .pass => .passed
  | .fail _ => .failed
  | .error _ => .error

/-- The message of a status that is not a pass. -/
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
  let chunk := OutputChunk.ofOutput o
  match chunks.back? with
  | some last =>
    if last.stream == chunk.stream then
      chunks.pop.push { last with text := last.text ++ chunk.text }
    else
      chunks.push chunk
  | none => chunks.push chunk

/--
The finished result {Lean.Doc.name}`r` as the widget shows it. {Lean.Doc.name}`id` identifies it
within the run, and {Lean.Doc.name}`parent` identifies the result that contains it. The result's
output is included when {Lean.Doc.name}`withOutput` is true. A failure's location is left out when
it is the test's own span, {Lean.Doc.name}`testLocation`.
-/
def ResultNode.ofResult (id parent : Nat) (testLocation : Location) (r : Result)
    (withOutput : Bool := true) : ResultNode where
  id := id
  parent := parent
  name := r.resultPath.back?.getD ""
  status? := some (verdictOf r.status)
  durationMs := r.durationMs
  message? := statusMessage r.status
  detail? := statusDetail r.status
  location? := statusLocation testLocation r.status
  output := if withOutput then r.output.log.foldl pushFragment #[] else #[]

private def nodesOfResults (testLocation : Location) (results : Array Result)
    (withOutput : Bool := true) : Array ResultNode := Id.run do
  let mut nodes : Array ResultNode := #[]
  -- The identifier of the result open at each depth, innermost last.
  let mut enclosing : Array Nat := #[]
  for r in results do
    let up := enclosing.extract 0 r.resultPath.size
    let id := nodes.size
    nodes := nodes.push (.ofResult id (up.back?.getD ResultNode.root) testLocation r withOutput)
    enclosing := up.push id
  return nodes

/--
Condenses the results of one test run into a single outcome. The verdict is the most severe status
present (error over failed over passed). The message and detail come from the innermost result
with that status, since a test's own result reports a named result's failure only in summary while
the named result reports the actual assertion that failed. Each result becomes a node with its own
output.

{name}`seed` is the seed for property tests, and {name}`testLocation` is the test's own source range,
which is used as a location of last resort. With {name}`onlyOwnResult`, the outcome holds one node,
for the test's own result, and that node's output is empty, for a caller that reads the output as the
test writes it.
-/
def summarizeResults (seed : Nat) (testLocation : Location) (results : Array Result)
    (onlyOwnResult : Bool := false) : RunOutcome := Id.run do
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
    results :=
      nodesOfResults testLocation
        (if onlyOwnResult then results.extract 0 1 else results)
        (withOutput := !onlyOwnResult)
    seed? := some (toString seed)
  }

/--
Runs one test entry to completion, as the batch runner does, and condenses its results into a
{name}`RunOutcome` whose description is the entry's docstring. Without a seed for property tests,
one is generated. {name}`options` are the options that the test reads, and the outcome names those
that it never read.

The test's output is passed to {name}`saveOutput` as it is written, and {name}`watch` is told as each
named result starts and finishes. A caller that wishes to monitor the run through them passes
{name}`onlyOwnResult`, and the outcome then holds only the test's own result, without its output.
Otherwise, the outcome holds every result, each with its own output.
-/
def runEntryOutcome (entry : TestEntry) (seed? : Option Nat := none)
    (saveOutput : Output → IO Unit := fun _ => pure ())
    (watch : ResultEvent → IO Unit := fun _ => pure ()) (onlyOwnResult : Bool := false)
    (options : OptionMap := {}) : IO RunOutcome := do
  let cfg := {
    ← mkContext (options := options) (seed := seed?) with
    writeOutput := saveOutput, watchResults := watch
  }
  let outcome := summarizeResults cfg.seed entry.location (← runEntry cfg entry) onlyOwnResult
  let read ← cfg.usedOptions.get
  let unreadOptions := options.keys.filter (!read.contains ·) |>.toArray.qsort (· < ·)
  return { outcome with description? := entry.docstring?, unreadOptions }

/-- Runs one testable value as {name}`runEntryOutcome` does, as a test with an empty name. -/
def runValue {α} [IsTest α] (location : Location) (value : α) (seed? : Option Nat := none)
    (saveOutput : Output → IO Unit := fun _ => pure ())
    (watch : ResultEvent → IO Unit := fun _ => pure ()) : IO RunOutcome :=
  runEntryOutcome (.of "" "" "" location value) seed? saveOutput watch
