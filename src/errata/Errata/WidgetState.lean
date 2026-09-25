/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
A run of one test as the run-test widget's server follows it: what the widget is sent, the run's
phase and the transitions between phases, and how the runner's events file drives them.
-/
module

public import Errata.Outcome
public import Errata.Protocol
public import Lean.Data.Json
public import Lean.Data.Lsp.Utf16

public section

set_option linter.missingDocs true
set_option doc.verso true

open Lean (Json ToJson FromJson)

namespace Errata.Widget

/-- An output stream that a test can write to. -/
inductive OutputChunk.Stream where
  /-- Standard output. -/
  | stdout
  /-- Standard error. -/
  | stderr
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq

/-- A run of captured output from a single stream, which the widget renders with the streams apart. -/
structure OutputChunk where
  /-- The stream the text was written to. -/
  stream : OutputChunk.Stream
  /-- The text written to that stream. -/
  text : String
  /-- When the text was written, in milliseconds since the Unix epoch, or {lean}`0` when unknown. -/
  time : Nat := 0
  /--
  The identifier of the named result that was open when the text was written, {lean}`0` for the test
  itself.
  -/
  result : Nat := 0
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq

/--
A source span as the editor counts it: a document, lines from zero, and columns in UTF-16 code
units.
-/
structure Source where
  /-- The document that contains the span. -/
  uri : String
  /-- The line the span starts on, counted from zero. -/
  startLine : Nat
  /-- The column the span starts at, in UTF-16 code units. -/
  startColumn : Nat
  /-- The line the span ends on, counted from zero. -/
  endLine : Nat
  /-- The column the span ends at, in UTF-16 code units. -/
  endColumn : Nat
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq

/--
The lines of source files, each file read once and kept, for the conversion of the codepoint columns
that the runner reports into the UTF-16 columns that the editor counts.
-/
structure SourceLines where
  /-- Each file read so far, with its lines, or {lean}`none` when it could not be read. -/
  files : IO.Ref (Array (System.FilePath × Option (Array String)))

/-- An empty cache of source lines. -/
def SourceLines.new : BaseIO SourceLines := return { files := ← IO.mkRef #[] }

/-- The lines of a file, read on the first request, or {lean}`none` when it cannot be read. -/
def SourceLines.linesOf (cache : SourceLines) (path : System.FilePath) :
    IO (Option (Array String)) := do
  if let some (_, lines) := (← cache.files.get).find? (·.1 == path) then return lines
  let lines ← try some <$> IO.FS.lines path catch _ => pure none
  cache.files.modify (·.push (path, lines))
  return lines

/--
The span of a location in Lean's form, a path with lines from one and codepoint columns, as the
editor counts it. The document's lines give the width of each codepoint; a file that cannot be read
keeps its codepoint columns.
-/
def Source.ofLocation (cache : SourceLines) (l : Location) : IO Source := do
  let lines ← cache.linesOf l.file
  let column (line codepoints : Nat) : Nat :=
    match lines.bind (·[line]?) with
    | some text => Lean.String.codepointPosToUtf16Pos text codepoints
    | none => codepoints
  let startLine := l.startPos.line - 1
  let endLine := l.endPos.line - 1
  return {
    uri := System.Uri.pathToUri l.file
    startLine, startColumn := column startLine l.startPos.column
    endLine, endColumn := column endLine l.endPos.column
  }

/--
One report from a result of a run: the test's own, identified by {lit}`0`, or a named result below
it. A named result is reported when it starts, with its identifier, parent, and name, and again when
it finishes, with its status.
-/
structure ResultNode where
  /-- The result's identifier within its run. -/
  id : Nat
  /-- The result that contains this one. -/
  parent : Nat := 0
  /-- The name the result was given; empty for the test's own. -/
  name : String := ""
  /--
  The status once the result has finished, as the protocol names it: {lit}`pass`, {lit}`fail`,
  {lit}`error`, or {lit}`expectedFailure`.
  -/
  status? : Option String := none
  /-- How long the result's own code took, in milliseconds. -/
  durationMs : Nat := 0
  /-- The failure or error message. -/
  message? : Option String := none
  /-- Supporting detail for a failure, such as a diff or a counterexample. -/
  detail? : Option String := none
  /-- Where the check that failed is. -/
  location? : Option Source := none
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq

/-- A fixture phase that ran for the test, as a step of the run. -/
structure Step where
  /-- The fixture's name. -/
  fixture : String
  /-- The fixture phase's path, such as the fixture's name followed by {lit}`setup`. -/
  path : Array String := #[]
  /--
  The phase's status: {lit}`pass`, {lit}`fail`, or {lit}`error` for a verdict, and
  {lit}`inconclusive` otherwise.
  -/
  status : String
  /-- What explains a phase that did not pass. -/
  message? : Option String := none
  /-- How long the phase took, in milliseconds. -/
  durationMs : Nat := 0
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq

/-- A run-level issue that the runner reported. -/
structure Issue where
  /-- {lit}`warning` or {lit}`error`. -/
  level : String
  /-- What the issue is. -/
  message : String
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq

/-- A setting's value that the run gave the test. -/
structure SettingValue where
  /-- The setting's name. -/
  name : String
  /-- The value, as the configuration gives it. -/
  value : String
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq

/--
How a run ended, as the widget shows it: the outcome that the runner reported for the test, or a
failure of the driver before the runner reported one.
-/
structure RunOutcome where
  /--
  The status: {lit}`pass`, {lit}`fail`, or {lit}`error` for a verdict, and {lit}`inconclusive` when
  the runner established none. A driver that ended before the runner reported an outcome gives
  {lit}`error`.
  -/
  status : String
  /--
  The message: a failure's or an error's, a sentence that explains an inconclusive outcome, or what
  went wrong with the driver.
  -/
  message? : Option String := none
  /-- Supporting detail, such as a diff, or the end of the driver's output. -/
  detail? : Option String := none
  /-- Where the failed check is, when it is somewhere other than the test's own declaration. -/
  location? : Option Source := none
  /-- The name of the inconclusive reason, for an inconclusive outcome. -/
  reason? : Option String := none
  /-- How long the test took by the runner's clock, in milliseconds. -/
  durationMs : Nat := 0
  /-- Whether the runner started the test, so that a duration and settings describe a run of it. -/
  ran : Bool := false
  /-- The seed the test received, as decimal digits, when it takes one. -/
  seed? : Option String := none
  /-- The values of the settings that the test received. -/
  settings : Array SettingValue := #[]
  /-- The test's docstring, as Markdown. -/
  description? : Option String := none
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq

/-- The outcome of a run that ended without an outcome for the test. -/
def RunOutcome.noTest : RunOutcome where
  status := "error"
  message? := some "the run ended without running the test"

/--
The report of the test's own result, from its outcome: identifier {lit}`0`, with the outcome's
status, message, detail, and location.
-/
def ResultNode.ofOutcome (o : RunOutcome) : ResultNode where
  id := 0
  status? := some o.status
  durationMs := o.durationMs
  message? := o.message?
  detail? := o.detail?
  location? := o.location?

/-- The phase of a run. -/
inductive Phase where
  /-- The driver is building what the run needs. -/
  | building
  /-- The runner is listing or running the test. -/
  | running
  /-- The run is over, with its outcome. -/
  | done (outcome : RunOutcome)
  /-- The run was cancelled before it produced an outcome. -/
  | cancelled
deriving Repr, Inhabited, DecidableEq

/-- Whether a run in this phase is still going. -/
def Phase.isLive : Phase → Bool
  | .building | .running => true
  | .done _ | .cancelled => false

/-- The phase's name as the widget receives it. -/
def Phase.name : Phase → String
  | .building => "building"
  | .running => "running"
  | .done _ => "done"
  | .cancelled => "cancelled"

/--
Everything about a run that changes as it goes. The server holds it in one reference, and every
change to it is a transition of {lit}`RunData.apply`, so each change sees and replaces the whole.
-/
structure RunData where
  /-- The run's phase. -/
  phase : Phase := .building
  /-- The output so far, in order. -/
  chunks : Array OutputChunk := #[]
  /-- The reports from the run's results so far, in order. -/
  results : Array ResultNode := #[]
  /-- The fixture phases that ran for the test, in order. -/
  steps : Array Step := #[]
  /-- The run-level issues that the runner reported, such as warnings about the configuration. -/
  issues : Array Issue := #[]
  /-- How long the driver took before the runner began, in milliseconds; {lean}`0` until then. -/
  buildMs : Nat := 0
  /-- When the test body started, in milliseconds since the Unix epoch; {lean}`0` until then. -/
  execStartTime : Nat := 0
  /-- The outcome that the runner reported for the test, which the run ends with. -/
  outcome? : Option RunOutcome := none
  /-- Kills the driver's process group, while the driver has yet to be found to have exited. -/
  kill? : Option (IO Unit) := none
  /-- Resolved when the run changes, which wakes the requests that wait on it. -/
  wakeup : IO.Promise Unit

/-- A change to a run. {lit}`RunData.apply` says which changes apply in which phases. -/
inductive Change where
  /-- The runner has begun its List phase, after the driver built for {name}`buildMs` ms. -/
  | listed (buildMs : Nat)
  /-- The test's body started at the given time. -/
  | execStart (timeMs : Nat)
  /-- Output arrived. -/
  | output (chunk : OutputChunk)
  /-- A result reported its start or its end. -/
  | result (node : ResultNode)
  /-- A fixture phase ran for the test. -/
  | step (step : Step)
  /-- The runner reported a run-level issue. -/
  | issue (issue : Issue)
  /-- The runner reported the test's outcome. -/
  | outcome (outcome : RunOutcome)
  /-- The runner ended the run. -/
  | ended
  /-- The driver exited; the run ends with the test's outcome, or with {name}`fallback`. -/
  | finish (fallback : RunOutcome)
  /-- The widget cancelled the run. -/
  | cancel
  /-- The driver started, and {name}`kill` ends it. -/
  | arm (kill : IO Unit)
  /-- The driver has exited, so its process group may no longer be signaled. -/
  | disarm

/--
The transition that a change makes: the run afterwards and an action to perform once the change is
in place, or {lean}`none` when the change does not apply in the run's phase, which leaves the run as
it was. Output, results, steps, issues, and outcomes arrive only while the run is live; a run ends once,
cancelled or done; a cancel's action is the driver's kill, and a driver that starts after a cancel
does not arm, so its caller ends it.
-/
def RunData.apply (d : RunData) : Change → Option (RunData × Option (IO Unit))
  | .listed buildMs =>
    if d.phase matches .building then some ({ d with phase := .running, buildMs }, none) else none
  | .execStart t => if d.phase.isLive then some ({ d with execStartTime := t }, none) else none
  | .output c => if d.phase.isLive then some ({ d with chunks := d.chunks.push c }, none) else none
  | .result n => if d.phase.isLive then some ({ d with results := d.results.push n }, none) else none
  | .step s => if d.phase.isLive then some ({ d with steps := d.steps.push s }, none) else none
  | .issue i => if d.phase.isLive then some ({ d with issues := d.issues.push i }, none) else none
  | .outcome o =>
    if d.phase.isLive && d.outcome?.isNone then
      some ({ d with outcome? := some o, results := d.results.push (.ofOutcome o) }, none)
    else none
  | .ended =>
    if d.phase.isLive then some ({ d with phase := .done (d.outcome?.getD .noTest) }, none) else none
  | .finish fallback =>
    if d.phase.isLive then some ({ d with phase := .done (d.outcome?.getD fallback) }, none)
    else none
  | .cancel =>
    if d.phase.isLive then some ({ d with phase := .cancelled, kill? := none }, d.kill?) else none
  | .arm kill => if d.phase.isLive then some ({ d with kill? := some kill }, none) else none
  | .disarm => if d.kill?.isSome then some ({ d with kill? := none }, none) else none

/-- A run of one test, as the server holds it: what identifies it, and its data in one reference. -/
structure RunState where
  /-- The identifier that the widget gave the run when it asked for it to start. -/
  runId : String
  /-- A hash of the test's source when the run started; a request with a different one is stale. -/
  version : String
  /-- When the run started, in milliseconds since the Unix epoch. -/
  startTime : Nat
  /-- A hash of the document's text when the run started. -/
  sourceHash : UInt64
  /-- The run's data, which changes only through {lit}`RunState.apply`. -/
  data : IO.Ref RunData

/-- A new run in its building phase. -/
def RunState.new (runId version : String) (startTime : Nat) (sourceHash : UInt64) :
    BaseIO RunState := do
  return { runId, version, startTime, sourceHash, data := ← IO.mkRef { wakeup := ← IO.Promise.new } }

/--
Applies a change to the run as one transition of {name}`RunData.apply`, and returns whether it
applied. A transition that applies replaces the run's wakeup promise in the same step and then
resolves the one it replaced, which wakes the requests waiting on the run, and then performs the
transition's action.
-/
def RunState.apply (s : RunState) (c : Change) : IO Bool := do
  let fresh ← IO.Promise.new
  let applied? ← s.data.modifyGet fun d =>
    match d.apply c with
    | some (d', act?) => (some (d.wakeup, act?), { d' with wakeup := fresh })
    | none => (none, d)
  match applied? with
  | none => return false
  | some (woken, act?) =>
    woken.resolve ()
    if let some act := act? then
      try act catch _ => pure ()
    return true

/--
Cancels the run when {name}`runId` is its identifier, and returns whether the cancel applied. A
request that names another run, or a run that is over, changes nothing.
-/
def RunState.cancelNamed (s : RunState) (runId : String) : IO Bool :=
  if s.runId == runId then s.apply .cancel else return false

/-- The run's phase. -/
def RunState.phase (s : RunState) : BaseIO Phase := return (← s.data.get).phase

/-- The fields of a JSON object, or none. -/
private def fieldOf? [FromJson α] (j : Json) (key : String) : Option α :=
  (j.getObjValAs? α key).toOption

/--
The report of a result from a {lit}`result` record of the events file, with its location as the
editor counts it. A location that is {Lean.Doc.name}`own?`, the test's own declaration, is left
out: a named result that failed because a result inside it did reports the test's declaration, and
the result inside it has the place of the failed check.
-/
def ResultNode.ofRecord (cache : SourceLines) (own? : Option Location) (j : Json) :
    IO ResultNode := do
  let location? ← match j.getObjVal? "location" with
    | .ok span =>
      let span : Protocol.Span := {
        file? := fieldOf? span "file", line? := fieldOf? span "line", col? := fieldOf? span "col"
        endLine? := fieldOf? span "endLine", endCol? := fieldOf? span "endCol"
      }
      if span.file?.isNone || some span.toLocation == own? then pure none
      else some <$> Source.ofLocation cache span.toLocation
    | .error _ => pure none
  return {
    id := (fieldOf? j "id").getD 0, parent := (fieldOf? j "parent").getD 0
    name := (fieldOf? j "name").getD "", status? := fieldOf? j "status"
    durationMs := (fieldOf? j "duration_ms").getD 0
    message? := fieldOf? j "message", detail? := fieldOf? j "detail", location?
  }

/--
The outcome in an {lit}`outcome` record of the events file. A failure's location is left out when
it is {name}`own?`, the test's own declaration, which the widget already shows the test at.
-/
def RunOutcome.ofRecord (cache : SourceLines) (own? : Option Location) (j : Json) :
    IO RunOutcome := do
  let settings := match j.getObjVal? "settings" >>= (·.getObj?) with
    | .ok obj => obj.toArray.filterMap fun (name, v) => v.getStr?.toOption.map ({ name, value := · })
    | .error _ => #[]
  let base : RunOutcome := {
    status := "error", durationMs := (fieldOf? j "duration_ms").getD 0, seed? := fieldOf? j "seed"
    settings, description? := fieldOf? j "description"
  }
  match Outcome.ofFields? j with
  | .error e => return { base with message? := some s!"the runner's outcome could not be read: {e}" }
  | .ok (.reported v) =>
    let (message?, detail?, location?) ← match v with
      | .pass => pure (none, none, none)
      | .error m => pure (some m, none, none)
      | .fail f =>
        let location? := f.location?.filter fun l => !l.file.isEmpty && some l != own?
        pure (some f.message, f.detail?, ← location?.mapM (Source.ofLocation cache))
    return { base with status := v.statusName, message?, detail?, location?, ran := true }
  | .ok (.inconclusive r) =>
    let ran := !(r matches .settingMissing _ | .fixtureFailed .. | .spawnFailed _)
    return { base with
      status := "inconclusive", message? := some r.describe, reason? := some r.reasonName, ran }

/-- The step that an {lit}`outcome` record of a fixture phase describes. -/
def Step.ofRecord (j : Json) : Step :=
  let (status, message?) := match Outcome.ofFields? j with
    | .ok (.reported .pass) => ("pass", none)
    | .ok (.reported (.fail f)) => ("fail", some f.message)
    | .ok (.reported (.error m)) => ("error", some m)
    | .ok (.inconclusive r) => ("inconclusive", some r.describe)
    | .error e => ("error", some e)
  { fixture := (fieldOf? j "test").getD "", path := (fieldOf? j "path").getD #[], status, message?
    durationMs := (fieldOf? j "duration_ms").getD 0 }

/--
The changes that one record of the runner's events file makes to the run of the test named
{name}`test`. The runner's {lit}`List` phase ends the building; the test's {lit}`start`,
{lit}`output`, and {lit}`result` records drive the display; its {lit}`outcome` is the result, and a
fixture phase's {lit}`outcome` is a step; an {lit}`issue` is kept with the run; {lit}`end` ends
the run. Records about other tests change nothing. {name}`startTime` is when the run began,
and {name}`own?` is the test's declaration, as {name}`RunOutcome.ofRecord` uses it.
-/
def changesOfRecord (cache : SourceLines) (test : String) (startTime : Nat) (own? : Option Location)
    (j : Json) : IO (Array Change) := do
  let about := (fieldOf? j "test" : Option String) == some test
  match (fieldOf? j "type" : Option String) with
  | some "phase" =>
    let time : Nat := (fieldOf? j "time_ms").getD startTime
    if (fieldOf? j "name" : Option String) matches some "List" | some "Run" then
      return #[.listed (time - startTime)]
    return #[]
  | some "issue" =>
    return #[.issue {
      level := (fieldOf? j "level").getD "warning", message := (fieldOf? j "message").getD "" }]
  | some "start" =>
    if about then return #[.execStart ((fieldOf? j "time_ms").getD 0)] else return #[]
  | some "output" =>
    unless about do return #[]
    let stream : OutputChunk.Stream :=
      if (fieldOf? j "stream" : Option String) == some "stderr" then .stderr else .stdout
    return #[.output {
      stream, text := (fieldOf? j "text").getD "", time := (fieldOf? j "time_ms").getD 0
      result := (fieldOf? j "result").getD 0 }]
  | some "result" =>
    if about then return #[.result (← ResultNode.ofRecord cache own? j)] else return #[]
  | some "outcome" =>
    if (fieldOf? j "kind" : Option String) == some "fixture" then return #[.step (Step.ofRecord j)]
    unless about do return #[]
    return #[.outcome (← RunOutcome.ofRecord cache own? j)]
  | some "end" => return #[.ended]
  | _ => return #[]

/--
The changes that one line of the runner's events file makes, as {name}`changesOfRecord` gives them.
A line that is not a JSON object changes nothing.
-/
def changesOfLine (cache : SourceLines) (test : String) (startTime : Nat) (own? : Option Location)
    (line : String) : IO (Array Change) :=
  match Json.parse line with
  | .ok j => changesOfRecord cache test startTime own? j
  | .error _ => pure #[]

end Errata.Widget
