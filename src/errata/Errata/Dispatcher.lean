/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The runner's dispatcher: every event of a run passes through one function, which updates the run's
state and says what the reporters and the events file receive. The human report, the events file,
and the final reports all see the events in the order that the function receives them.
-/
module

public import Errata.Report
public import Errata.Protocol
public import Lean.Data.Json

public section

set_option linter.missingDocs true
set_option doc.verso true

open Lean (Json ToJson)

namespace Errata.Runner

/-- A test that the runner is about to run, with everything it passes to the test executable. -/
structure Planned where
  /-- The test executable's name. -/
  exe : String
  /-- The test's name. -/
  test : String
  /-- The components of the test's name, for nesting in reports. -/
  path : Array String := #[]
  /-- The test's description from the inventory. -/
  description? : Option String := none
  /-- The seed that the test receives, when it takes the setting {lit}`Errata.seed`. -/
  seed? : Option String := none
  /-- The settings that the test receives, in order, the seed among them. -/
  settings : Array (String × String) := #[]
  /-- The command line that runs the test by hand. -/
  reproduce : String
  /-- How long the test may run before the report marks it slow, in milliseconds. -/
  slowAfterMs : Nat := 60 * 1000
deriving Repr, Inhabited

/-- How a test executable's process ended, as the runner observed it. -/
inductive Exit where
  /-- The process exited with this code. -/
  | exited (code : UInt32)
  /-- The process ran past its timeout; {name}`killed` says whether the kill was needed. -/
  | timedOut (afterMs : Nat) (killed : Bool)
  /-- The process could not be started. -/
  | spawnFailed (message : String)
  /-- The mandatory setting {name}`setting` has no value, so the runner started no process. -/
  | settingMissing (setting : String)
deriving Repr, Inhabited

/-- Something that happened during a run. -/
inductive Event where
  /-- A phase of the run has begun. -/
  | phase (name : String) (timeMs : Nat)
  /-- An issue with the run as a whole. -/
  | issue (issue : RunReport.Issue)
  /-- A test is about to be started. -/
  | testStarted (test : Planned)
  /-- A record arrived from a test executable's result file, as JSON and decoded. -/
  | record (exe test : String) (json : Json) (record : Protocol.Record)
  /-- A line arrived on a test executable's standard output or standard error. -/
  | captured (exe test : String) (stream : String) (text : String) (timeMs : Nat)
  /-- A line of a test executable's result file could not be read. -/
  | unreadable (exe test : String) (message : String)
  /-- A test executable's process has ended, after {name}`durationMs` milliseconds. -/
  | testEnded (exe test : String) (exit : Exit) (durationMs : Nat)
  /--
  The run is over. The human report prints its summary when {name}`summary` is true, with the number
  of tests that the filters left out when {name}`skipped?` gives it.
  -/
  | ended (timeMs : Nat) (summary : Bool) (skipped? : Option Nat)
deriving Inhabited

/-- What the dispatcher asks of the reporters. -/
inductive Action where
  /-- Append a line to the events file. -/
  | event (json : Json)
  /-- Print a line of the human-readable report. -/
  | print (line : String)
deriving Inhabited

/-- A named result that a test executable reported. -/
structure Node where
  /-- The result's identifier. -/
  id : Nat
  /-- The identifier of the result that contains it. -/
  parent : Nat
  /-- The result's name. -/
  name : String
  /-- The latest report of its finish, if it has finished. -/
  finish? : Option Protocol.ResultInfo := none
  /-- What it wrote. -/
  output : Array Output := #[]
deriving Inhabited

/-- What the dispatcher knows about a test that is running. -/
structure Running where
  /-- The test and how it was started. -/
  planned : Planned
  /-- What the test wrote outside every named result, and what its process wrote. -/
  output : Array Output := #[]
  /-- The named results, in the order they started. -/
  nodes : Array Node := #[]
  /-- The test's verdict, once it has reported one. -/
  verdict? : Option Protocol.VerdictInfo := none
  /-- Why the result file could not be read, if it could not. -/
  unreadable? : Option String := none
  /-- Whether a record of the result file has arrived. -/
  sawRecord : Bool := false
deriving Inhabited

/-- The dispatcher's state. -/
structure State where
  /-- The human-readable reporter. -/
  human : HumanReporter
  /-- Whether warnings count as errors. -/
  wfail : Bool := false
  /-- When the run started, in milliseconds since the epoch. -/
  startMs : Nat := 0
  /-- The tests that are running. -/
  running : Array Running := #[]
  /-- The results of the tests that have finished, in the order they finished. -/
  results : Array Result := #[]
  /-- The issues with the run as a whole. -/
  issues : Array RunReport.Issue := #[]
deriving Inhabited

/-- Adds the executable's and the test's names to a record from a test executable. -/
def tagged (exe test : String) (j : Json) : Json :=
  (j.setObjVal! "exe" (.str exe)).setObjVal! "test" (.str test)

/--
The verdict that a record's status, message, detail, and location stand for. An expected failure
stands for a pass.
-/
def verdictOfInfo (status : Protocol.Status) (message? detail? : Option String)
    (location? : Option Protocol.Span) : Verdict :=
  match status with
  | .pass | .expectedFailure => .pass
  | .fail => .fail {
      message := message?.getD "failed", detail?, location? := location?.map (·.toLocation)
    }
  | .error => .error (message?.getD "error")

/--
The number of the signal that an exit code reports, if it reports one. The system reports a signal
as {lit}`128` plus the signal's number, and the codes {lit}`129` to {lit}`192` are read as signals.
-/
def signalOfExitCode? (code : UInt32) : Option Nat :=
  if code > 128 && code ≤ 128 + 64 then some (code.toNat - 128) else none

/--
Merges what the test executable reported with how its process ended. The exit code is the floor: a
zero exit with no verdict is a pass, a non-zero exit with no verdict is
{name}`Inconclusive.exitedWithoutVerdict`, and a verdict that contradicts the exit code is
{name}`Inconclusive.verdictMismatch`.
-/
def mergeOutcome (verdict? : Option Protocol.VerdictInfo) (unreadable? : Option String)
    (exit : Exit) : Outcome :=
  match exit with
  | .settingMissing s => .inconclusive (.settingMissing s)
  | .spawnFailed m => .inconclusive (.spawnFailed m)
  | .timedOut ms killed => .inconclusive (.timedOut ms killed)
  | .exited code =>
    if let some s := signalOfExitCode? code then .inconclusive (.signaled s)
    else if let some e := unreadable? then .inconclusive (.resultStreamUnreadable e)
    else
      let claimed? := verdict?.bind fun v =>
        v.status?.map (verdictOfInfo · v.message? v.detail? v.location?)
      match claimed?, code with
      | none, 0 => .reported .pass
      | none, c => .inconclusive (.exitedWithoutVerdict c)
      | some .pass, 0 => .reported .pass
      | some v, 0 => .inconclusive (.verdictMismatch 0 v)
      | some .pass, c => .inconclusive (.verdictMismatch c .pass)
      | some v, _ => .reported v

/--
The named results of a finished test, as results below the test's own. A named result starts after
the result that contains it, so the nodes are in an order in which each parent precedes its children,
and each node's path extends its parent's. A node whose parent is unknown is placed directly below
the test.
-/
def nodeResults (p : Planned) (nodes : Array Node) : Array Result := Id.run do
  let mut paths : Std.HashMap Nat (Array String) := {}
  let mut out := #[]
  for n in nodes do
    let path := (paths.getD n.parent #[]).push n.name
    paths := paths.insert n.id path
    let outcome : Outcome ←
      match n.finish? with
      | none => pure (.reported (.error "the named result did not finish"))
      | some info =>
        match info.status? with
        | some .expectedFailure => continue
        | some st => pure (.reported (verdictOfInfo st info.message? info.detail? info.location?))
        | none => pure (.reported (.error "the named result did not finish"))
    out := out.push {
      exe := p.exe, test := p.test, path := p.path
      resultPath := path
      outcome, durationMs := (n.finish?.bind (·.durationMs?)).getD 0
      output := { log := n.output }
    }
  return out

/-- The results of a finished test: its own, then its named results. -/
def testResults (r : Running) (exit : Exit) (durationMs : Nat) : Array Result :=
  let p := r.planned
  let outcome := mergeOutcome r.verdict? r.unreadable? exit
  let named := nodeResults p r.nodes
  let inside := named.foldl (· + ·.durationMs) 0
  let own : Result := {
    exe := p.exe, test := p.test, path := p.path, outcome
    durationMs := durationMs - inside
    output := { log := r.output }
    description? := p.description?
    reproduce? := if outcome.isPass || exit matches .settingMissing _ then none else some p.reproduce
    settings := p.settings
    slow := durationMs ≥ p.slowAfterMs
  }
  #[own] ++ named

/-- The events-file record for a test's outcome. -/
def outcomeEvent (p : Planned) (outcome : Outcome) (durationMs : Nat) : Json :=
  Json.mkObj <|
    [("type", Json.str "outcome"), ("exe", Json.str p.exe), ("test", Json.str p.test),
      ("kind", Json.str "test"), ("path", ToJson.toJson p.path)] ++
    outcome.fields ++
    [("duration_ms", ToJson.toJson durationMs)] ++
    (match p.seed? with | some s => [("seed", Json.str s)] | none => []) ++
    [("settings", Json.mkObj (p.settings.toList.map fun (k, v) => (k, Json.str v)))] ++
    (match p.description? with | some d => [("description", Json.str d)] | none => []) ++
    (if outcome.isPass then [] else [("reproduce", Json.str p.reproduce)])

/-- Applies a function to the running test with the given names, if there is one. -/
private def State.modifyRunning (s : State) (exe test : String) (f : Running → Running) : State :=
  match s.running.findIdx? (fun r => r.planned.exe == exe && r.planned.test == test) with
  | some i => { s with running := s.running.modify i f }
  | none => s

/-- Adds output to the named result with the given identifier, or to the test's own. -/
private def Running.addOutput (r : Running) (result : Nat) (o : Output) : Running :=
  match r.nodes.findIdx? (·.id == result) with
  | some i => if result == 0 then { r with output := r.output.push o }
    else { r with nodes := r.nodes.modify i fun n => { n with output := n.output.push o } }
  | none => { r with output := r.output.push o }

/-- Takes in a record from a test executable's result file, whatever its place in the file. -/
private def Running.addKnownRecord (r : Running) : Protocol.Record → Running
  | .output stream? text? _ result? =>
    let text := text?.getD ""
    let o : Output := if stream? == some "stderr" then .stderr text else .stdout text
    r.addOutput (result?.getD 0) o
  | .result info =>
    match info.id? with
    | none | some 0 => r
    | some id =>
      match r.nodes.findIdx? (·.id == id) with
      | some i =>
        if info.status?.isSome then
          { r with nodes := r.nodes.modify i fun n => { n with finish? := some info } }
        else r
      | none =>
        { r with nodes := r.nodes.push {
            id, parent := info.parent?.getD 0, name := info.name?.getD ""
            finish? := if info.status?.isSome then some info else none } }
  | .verdict info =>
    if r.verdict?.isSome then
      { r with unreadable? := r.unreadable? <|> some "the result file holds two verdict records" }
    else { r with verdict? := some info }
  | _ => r

/--
Takes in a record from a test executable's result file. The first record must be the
{lit}`protocol` record; any other makes the result file unreadable.
-/
private def Running.addRecord (r : Running) (rec : Protocol.Record) : Running :=
  let first := !r.sawRecord && !(rec matches .protocol _)
  let unreadable? :=
    if first then r.unreadable? <|> some "the result file does not begin with a protocol record"
    else r.unreadable?
  { r with sawRecord := true, unreadable? }.addKnownRecord rec

/--
The line with which the human-readable report names a phase as it begins, at a verbosity that shows
passes.
-/
def phaseLine (name : String) : String := s!"== {name}"

/--
Handles one event: the new state, and what the reporters and the events file receive. An event about
a test that is not running comes from a process that outlived its test, and it is ignored.
-/
def step (s : State) : Event → State × Array Action
  | .phase name timeMs =>
    let event := Action.event (Json.mkObj [("type", Json.str "phase"), ("name", Json.str name),
      ("time_ms", ToJson.toJson timeMs)])
    (s, if s.human.verbosity.showsPasses then #[event, .print (phaseLine name)] else #[event])
  | .issue issue =>
    let issue := if s.wfail then { issue with isError := true } else issue
    ({ s with issues := s.issues.push issue }, #[.event (Json.mkObj
      [("type", Json.str "issue"), ("level", Json.str issue.level),
        ("message", Json.str issue.message)])])
  | .testStarted p => ({ s with running := s.running.push { planned := p } }, #[])
  | .record exe test json rec =>
    if !(s.running.any fun r => r.planned.exe == exe && r.planned.test == test) then (s, #[])
    else
      let s := s.modifyRunning exe test (·.addRecord rec)
      let forwarded := match rec with
        | .start .. | .output .. | .result .. => #[Action.event (tagged exe test json)]
        | _ => #[]
      (s, forwarded)
  | .captured exe test stream text timeMs =>
    if !(s.running.any fun r => r.planned.exe == exe && r.planned.test == test) then (s, #[])
    else
      let o : Output := if stream == "stderr" then .stderr text else .stdout text
      let s := s.modifyRunning exe test (·.addOutput 0 o)
      (s, #[.event (Json.mkObj [("type", Json.str "output"), ("exe", Json.str exe),
        ("test", Json.str test), ("stream", Json.str stream), ("text", Json.str text),
        ("time_ms", ToJson.toJson timeMs), ("result", ToJson.toJson (0 : Nat))])])
  | .unreadable exe test message =>
    (s.modifyRunning exe test fun r =>
      if r.unreadable?.isSome then r else { r with unreadable? := some message }, #[])
  | .testEnded exe test exit durationMs =>
    match s.running.findIdx? (fun r => r.planned.exe == exe && r.planned.test == test) with
    | none => (s, #[])
    | some i =>
      let r := s.running[i]!
      let results := testResults r exit durationMs
      let outcome := (results[0]?.map (·.outcome)).getD (.reported .pass)
      let (human, lines) := s.human.test results
      let s := { s with
        running := s.running.eraseIdx! i, results := s.results ++ results, human }
      (s, #[.event (outcomeEvent r.planned outcome durationMs)] ++ lines.map .print)
  | .ended timeMs summary skipped? =>
    let t := s.human.tally
    let line := s.human.summary (timeMs - s.startMs) skipped?
    (s, (if summary then #[.print line] else #[]) ++ #[.event (Json.mkObj [("type", Json.str "end"),
      ("time_ms", ToJson.toJson timeMs), ("passed", ToJson.toJson t.passed),
      ("failed", ToJson.toJson t.failed), ("errors", ToJson.toJson t.errors),
      ("inconclusive", ToJson.toJson t.inconclusive)])])
