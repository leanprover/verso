/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public meta import Lean.Widget.UserWidget
public meta import Lean.Server
public meta import Std.Time
public meta import Errata.NameJson
public meta import Errata.RunOne

public section

set_option linter.missingDocs true
set_option doc.verso true

open Lean

namespace Errata.Widget

/--
Shown when the text cursor is on a test's source span. It offers a "run" button that runs the test
in the language server, streaming its output as it is produced.
-/
@[widget_module]
meta def runTestWidget : Lean.Widget.Module where
  javascript := include_str "widget/run_test_widget.js"

/-- The current wall-clock time in milliseconds since the Unix epoch. -/
private meta def nowMs : IO Nat :=
  return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat

/--
A live (or just-finished) run. Output chunks accumulate in {name (full := RunState.chunks)}`chunks`
so a widget that reconnects after the cursor leaves and returns can replay them by index. The wakeup
promise is resolved and replaced whenever a chunk arrives or the run finishes, waking any waiter.
-/
meta structure RunState where
  /-- Every output chunk produced so far, in order. -/
  chunks : IO.Ref (Array Errata.OutputChunk)
  /--
  The reports from named results so far, in order. A named result is reported when it starts, with
  its identifier, parent, and name, and again when it finishes, with its verdict.
  -/
  results : IO.Ref (Array Errata.ResultNode)
  /-- Whether the run has finished. -/
  finished : IO.Ref Bool
  /-- The final outcome, set when the run finishes. -/
  outcome : IO.Ref (Option Errata.RunOutcome)
  /-- A promise resolved and replaced on each change, used to wake waiters without polling. -/
  wakeup : IO.Ref (IO.Promise Unit)
  /-- The current phase, {lit}`"building"` while compiling the module then {lit}`"running"`. -/
  phase : IO.Ref String
  /-- A hash of the test's source when the run started; a later request with a different one is stale. -/
  version : String
  /-- When the run started, in milliseconds since the Unix epoch. -/
  startTime : Nat
  /-- How long the build took, in milliseconds; 0 while still building. -/
  buildMs : IO.Ref Nat
  /-- When the test body started (reported by the runner), in epoch ms; 0 until then. -/
  execStartTime : IO.Ref Nat
  /--
  The process to be killed if the run is cancelled. Contains first the build, then the runner.
  Updated as each is spawned.
  -/
  kill : IO.Ref (IO Unit)
  /-- A hash of the document's text when the run started. -/
  sourceHash : UInt64

/-- The live runs, keyed by the test's declaration name so a run survives re-elaboration. -/
meta initialize runRegistry : IO.Ref (Std.HashMap Name RunState) ← IO.mkRef {}

/-- A request to start running a test: the declaration and the module that defines it. -/
meta structure StartRequest where
  /-- The test declaration to run, encoded by {name}`nameToJson`. -/
  decl : Json
  /-- The module that defines the test, encoded by {name}`nameToJson`. -/
  module : Json
  /-- A hash of the test's source, recorded with the run so an edit can invalidate it. -/
  version : String
  /--
  The seed for property tests, or {lean}`none` to have one randomly generated. Because JavaScript
  represents JSON numbers as floats, cutting off their range, it is a string of decimal digits.
  -/
  seed? : Option String := none
deriving Lean.FromJson, Lean.ToJson

/-- A request for output past a known position, naming the test by its encoded declaration. -/
meta structure AwaitRequest where
  /-- The test declaration, encoded by {name}`nameToJson`. -/
  decl : Json
  /-- The number of chunks the widget already has, so only later ones are returned. -/
  since : Nat
  /--
  The number of reports from named results that the widget already has, counted the same way as
  {name (full := AwaitRequest.since)}`since`.
  -/
  sinceResults : Nat := 0
  /-- The test's source hash; a run recorded under a different one is stale and ignored. -/
  version : String
  /-- The phase the widget last saw; a reply is returned at once when the run's phase differs. -/
  phase : String
deriving Lean.FromJson, Lean.ToJson

/-- A request that names a running test by its declaration, encoded by {name}`nameToJson`. -/
meta structure RunRef where
  /-- The test declaration, encoded by {name}`nameToJson`. -/
  decl : Json
deriving Lean.FromJson, Lean.ToJson

/-- A request that names the run of one version of a test. -/
meta structure VersionRef where
  /-- The test declaration, encoded by {name}`nameToJson`. -/
  decl : Json
  /-- The source hash the run was recorded under. -/
  version : String
deriving Lean.FromJson, Lean.ToJson

/-- One reply from {lit}`awaitOutput`: any output chunks past the requested position, or the outcome. -/
meta structure AwaitResult where
  /-- The output chunks past the requested position. -/
  chunks : Array Errata.OutputChunk := #[]
  /-- The position past the returned chunks, to pass as the next request's start. -/
  nextSince : Nat := 0
  /--
  The reports from named results that are newer than those the widget already has. A named result
  is reported when it starts and again when it finishes.
  -/
  results : Array Errata.ResultNode := #[]
  /--
  How many reports from named results the run has made so far. The widget sends this back with its
  next request, as the number of reports it already has.
  -/
  nextSinceResults : Nat := 0
  /-- When the run started, in milliseconds since the Unix epoch. -/
  startTime : Nat := 0
  /--
  How long ago the run started, in milliseconds by the server's clock. The widget's elapsed counter
  ticks from it, so the display stays right when the server's clock differs from the editor's.
  -/
  elapsedMs : Nat := 0
  /-- How long the build took, in milliseconds; 0 while still building. -/
  buildMs : Nat := 0
  /-- When the test body started, in epoch ms; 0 until then. Output offsets are relative to it. -/
  execStartTime : Nat := 0
  /-- The current phase, {lit}`"building"` or {lit}`"running"`. -/
  phase : String := "running"
  /-- Whether the run has finished and no more output will arrive. -/
  done : Bool := false
  /-- The final outcome, present once {lit}`done` is set. -/
  outcome : Option Errata.RunOutcome := none
deriving Lean.FromJson, Lean.ToJson

open Server in
/-- Decodes the declaration name from a request, failing the request if it is malformed. -/
private meta def decodeDecl (j : Json) : RequestM Name :=
  match nameOfJson? j with
  | .ok n => pure n
  | .error e => throw (.mk .invalidParams e)

/-- Resolves the run's current wakeup promise and installs a fresh one, waking any waiter. -/
private meta def signalRun (state : RunState) : IO Unit := do
  let p ← state.wakeup.get
  state.wakeup.set (← IO.Promise.new)
  p.resolve ()

/-- Marks a run finished, kills its process, and wakes its waiters. -/
private meta def stopRun (state : RunState) : IO Unit := do
  state.finished.set true
  try (← state.kill.get) catch _ => pure ()
  signalRun state

/--
Forgets the run of a name, if any, and stops it. The run is taken out of the registry in the same
step that finds it, so a run that a concurrent request has just started stays in place.
{name}`onlyIf` picks which runs are dropped.
-/
private meta def dropRun (declName : Name) (onlyIf : RunState → Bool := fun _ => true) :
    IO Unit := do
  let taken ← runRegistry.modifyGet fun runs =>
    match runs.get? declName with
    | some state => if onlyIf state then (some state, runs.erase declName) else (none, runs)
    | none => (none, runs)
  if let some state := taken then stopRun state

/--
Records how to kill the process a run is waiting on. A run that was cancelled before this point
kills the process at once, and the result is {lean}`false`.
-/
private meta def setKill (state : RunState) (kill : IO Unit) : IO Bool := do
  state.kill.set kill
  if (← state.finished.get) then
    try kill catch _ => pure ()
    return false
  return true

/--
Ends a run, with {name}`fallback` as its outcome when the runner reported none. A run that was
cancelled earlier keeps its state.
-/
private meta def finishWith (state : RunState) (fallback : Errata.RunOutcome) : IO Unit := do
  if (← state.finished.get) then return
  if (← state.outcome.get).isNone then state.outcome.set (some fallback)
  state.finished.set true
  signalRun state

/--
Reads the runner's JSON protocol from its stdout: a {lit}`chunk` line per output fragment, then an
{lit}`outcome` line. Returns at end of input, which is reached when the process exits or is killed.
-/
private meta partial def readLoop (out : IO.FS.Handle) (state : RunState) : IO Unit := do
  let line ← out.getLine
  if line.isEmpty then return
  if let .ok j := Json.parse line then
    if let .ok c := j.getObjVal? "chunk" then
      if let .ok chunk := (fromJson? c : Except String Errata.OutputChunk) then
        state.chunks.modify (·.push chunk)
        signalRun state
    else if let .ok n := j.getObjVal? "result" then
      if let .ok node := (fromJson? n : Except String Errata.ResultNode) then
        state.results.modify (·.push node)
        signalRun state
    else if let .ok ex := j.getObjVal? "exec" then
      if let .ok t := (fromJson? ex : Except String Nat) then
        state.execStartTime.set t
        signalRun state
    else if let .ok o := j.getObjVal? "outcome" then
      if let .ok oc := (fromJson? o : Except String Errata.RunOutcome) then
        state.outcome.set oc
  readLoop out state

/-- The number of characters of a failed subprocess's output to be reported. -/
private meta def detailLimit : Nat := 4000

/--
The end of a subprocess's output, which is where it says what went wrong: its last
{name}`detailLimit` characters. A build that fails after a long log then sends the widget a reply of
a few kilobytes.
-/
private meta def endOf (text : String) : String :=
  if text.length ≤ detailLimit then text
  else "…\n" ++ text.drop (text.length - detailLimit)

/-- The outcome shown when the build step fails, carrying its message and detail. -/
private meta def buildFailure (detail : String) : Errata.RunOutcome := {
  status := .error, durationMs := 0, message? := some "lake build failed"
  detail? := some (endOf detail)
}

/-- The outcome shown when building or running the test raises an error, such as a failed spawn. -/
private meta def launchFailure (e : IO.Error) : Errata.RunOutcome := {
  status := .error, durationMs := 0, message? := some s!"the test could not be run: {e}"
}

/-- The outcome shown when the runner exits without reporting one: its exit code and stderr. -/
private meta def runnerFailure (code : UInt32) (stderr : String) : Errata.RunOutcome := {
  status := .error, durationMs := 0
  message? := some s!"the test runner exited with code {code} before reporting an outcome"
  detail? := if stderr.trimAscii.isEmpty then none else some (endOf stderr)
}

/--
Builds the test's module from the saved source, then runs the test, streaming its output into the
run state. Building first means a Run reflects the latest saved version of the test.
{name}`source` is the file that defines the test, and {name}`moduleJson` and {name}`declJson` are
the module and the test declaration, encoded by {name}`nameToJson`. {name}`seed?` is the seed for
property tests, or {lean}`none` to have the runner draw one.
-/
private meta def buildAndRun (source : System.FilePath) (moduleJson declJson : String)
    (seed? : Option Nat) (state : RunState) : IO Unit := do
  -- `lake query` builds the runner exe and the module of the given source file (so the run reflects
  -- the saved source) and prints the exe's absolute path on stdout; progress and errors go to
  -- stderr. The file names exactly one module, whatever characters its name contains.
  let build ← IO.Process.spawn {
    stdin := .null, stdout := .piped, stderr := .piped
    cmd := "lake", args := #["query", "errata-run-one", source.toString]
  }
  unless ← setKill state build.kill do
    let _ ← build.wait
    return
  let errTask ← IO.asTask (prio := .dedicated) build.stderr.readToEnd
  let queryOut ← build.stdout.readToEnd
  let buildErr := (← IO.wait errTask).toOption.getD ""
  if (← build.wait) != 0 then
    finishWith state (buildFailure buildErr)
    return
  let some runnerPath := (queryOut.splitOn "\n").find? (!·.trimAscii.isEmpty) |>.map (·.trimAscii.copy)
    | finishWith state (buildFailure "lake query did not report the runner's path")
      return
  -- A run cancelled while its build finished ends here.
  if (← state.finished.get) then return
  -- The runner inherits the language server's `LEAN_PATH`, which reaches every module of the
  -- workspace, including the test module that it imports at runtime.
  let run ← IO.Process.spawn {
    stdin := .null, stdout := .piped, stderr := .piped
    cmd := runnerPath, args := #[moduleJson, declJson] ++ (seed?.map (#[toString ·])).getD #[]
  }
  unless ← setKill state run.kill do
    let _ ← run.wait
    return
  state.buildMs.set ((← nowMs) - state.startTime)
  state.phase.set "running"
  signalRun state
  -- The runner's stderr has anything that went wrong outside the test body, such as a failed
  -- import; it becomes the outcome's detail when the runner reports no outcome of its own.
  let runErrTask ← IO.asTask (prio := .dedicated) run.stderr.readToEnd
  readLoop run.stdout state
  let code ← run.wait
  let runErr := (← IO.wait runErrTask).toOption.getD ""
  finishWith state (runnerFailure code runErr)

open Server in
/-- Whether the document's live text matches what is on disk, i.e. it has no unsaved changes. -/
private meta def bufferIsClean : RequestM Bool := do
  let docMeta := (← RequestM.readDoc).meta
  let some path := System.Uri.fileUriToPath? docMeta.uri
    | return true
  match (← (IO.FS.readFile path).toBaseIO).toOption with
  | some disk => return docMeta.text.source == disk.crlfToLf
  | none => return true

/-- The state of a test's file, as its widget shows it beside the Run button. -/
meta structure FileState where
  /-- Whether the document has no unsaved changes, which a run needs. -/
  clean : Bool
  /-- Whether the document has changed since the test's run started, so its result is stale. -/
  changedSinceRun : Bool
deriving Lean.FromJson, Lean.ToJson

open Server in
/--
Server RPC method reporting the state of a test's file: whether it has unsaved changes, which gates
the Run button, and whether it has changed since the test's run started.
-/
@[server_rpc_method]
meta def fileState (req : RunRef) : RequestM (RequestTask FileState) := do
  let declName ← decodeDecl req.decl
  let source := (← RequestM.readDoc).meta.text.source
  let changedSinceRun := match (← runRegistry.get).get? declName with
    | some state => state.sourceHash != source.hash
    | none => false
  return RequestTask.pure { clean := ← bufferIsClean, changedSinceRun }

open Server in
/-- Server RPC method that starts running a test: builds its saved source, then streams its output. -/
@[server_rpc_method]
meta def startTest (req : StartRequest) : RequestM (RequestTask Unit) := do
  let declName ← decodeDecl req.decl
  let seed? ← req.seed?.mapM fun s =>
    match s.toNat? with
    | some seed => pure seed
    | none =>
      throw (.mk .invalidParams s!"the seed must be a natural number in decimal digits: {s}")
  let _ ← decodeDecl req.module
  let some source := System.Uri.fileUriToPath? (← RequestM.readDoc).meta.uri
    | throw (.mk .invalidParams "the test's document is not a file")
  unless ← bufferIsClean do
    throw (.mk .invalidParams "the file has unsaved changes; save it before running the test")
  let state : RunState := {
    chunks := ← IO.mkRef #[], results := ← IO.mkRef #[],
    finished := ← IO.mkRef false, outcome := ← IO.mkRef none,
    wakeup := ← IO.mkRef (← IO.Promise.new), phase := ← IO.mkRef "building", version := req.version,
    startTime := ← nowMs, buildMs := ← IO.mkRef 0, execStartTime := ← IO.mkRef 0,
    kill := ← IO.mkRef (pure ()), sourceHash := (← RequestM.readDoc).meta.text.source.hash
  }
  -- The new run replaces the previous one in the same step that finds it.
  let previous? ← runRegistry.modifyGet fun runs => (runs.get? declName, runs.insert declName state)
  if let some previous := previous? then stopRun previous
  -- The task spends most of its time blocked on the build and the runner, so it has its own thread.
  let _ ← IO.asTask (prio := .dedicated) do
    try buildAndRun source req.module.compress req.decl.compress seed? state
    catch e => finishWith state (launchFailure e)
  return RequestTask.pure ()

open Server in
/--
Builds the reply for a waiter given the run's current state and the position it already has. The
chunks past that position come together with the run's completion status, so a widget that
reconnects to a finished run settles in a single reply.
-/
private meta def replyFrom (state : RunState) (since sinceResults : Nat) : IO AwaitResult := do
  -- The finished flag is read before the chunks: once it is set, every chunk has been recorded, so
  -- a reply that says done carries all of them.
  let done ← state.finished.get
  let outcome ← state.outcome.get
  let chunks ← state.chunks.get
  let phase ← state.phase.get
  let startTime := state.startTime
  let elapsedMs := (← nowMs) - startTime
  let buildMs ← state.buildMs.get
  let execStartTime ← state.execStartTime.get
  let results ← state.results.get
  return {
    chunks := chunks.extract since chunks.size, nextSince := chunks.size
    results := results.extract sinceResults results.size, nextSinceResults := results.size
    phase, startTime, elapsedMs, buildMs, execStartTime, done, outcome
  }

open Server in
/--
Server RPC method that returns output chunks past {name (full := AwaitRequest.since)}`since`, or the
final outcome. When nothing new is available yet, the reply hangs off the run's wakeup promise, so no
worker thread is held while waiting and a reconnecting widget replays from {lit}`since := 0`.
-/
@[server_rpc_method]
meta def awaitOutput (req : AwaitRequest) : RequestM (RequestTask AwaitResult) := do
  let declName ← decodeDecl req.decl
  let some state := (← runRegistry.get).get? declName
    | return RequestTask.pure ({ done := true } : AwaitResult)
  -- A run recorded under a different source hash is from before an edit; treat it as absent.
  if state.version != req.version then
    return RequestTask.pure ({ done := true } : AwaitResult)
  let p ← state.wakeup.get
  let chunks ← state.chunks.get
  let results ← state.results.get
  -- Return at once when there is new output, a named result has started or finished, the run
  -- finished, or its phase changed (so a widget reconnecting mid-build learns it is building rather
  -- than waiting silently); otherwise wait.
  if chunks.size > req.since || results.size > req.sinceResults || (← state.finished.get) ||
      (← state.phase.get) != req.phase then
    return RequestTask.pure (← replyFrom state req.since req.sinceResults)
  RequestM.mapTaskCheap (p.resultD ()).asServerTask fun _ =>
    liftM (replyFrom state req.since req.sinceResults)

open Server in
/--
Server RPC method that ends the run of a test's source as it was before an edit. The run is dropped
when the hash it was recorded under is the one given, so a run of the test's current source keeps
going.
-/
@[server_rpc_method]
meta def dropStaleRun (req : VersionRef) : RequestM (RequestTask Unit) := do
  let declName ← decodeDecl req.decl
  dropRun declName (onlyIf := (·.version == req.version))
  return RequestTask.pure ()

open Server in
/-- Server RPC method that cancels a running test by killing its process. -/
@[server_rpc_method]
meta def cancelTest (req : RunRef) : RequestM (RequestTask Unit) := do
  let declName ← decodeDecl req.decl
  dropRun declName
  return RequestTask.pure ()
