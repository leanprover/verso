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
The InfoView widget shown when the text cursor is on a test's {lit}`@[test]` marker. It offers a Run
button that runs the test in the language server, streaming its output as it is produced.
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

/-- The live runs, keyed by the test's declaration name so a run survives re-elaboration. -/
meta initialize runRegistry : IO.Ref (Std.HashMap Name RunState) ← IO.mkRef {}

/-- A request to start running a test: the declaration and the module that defines it. -/
meta structure StartRequest where
  /-- The test declaration to run, encoded by {name}`nameToJson`. -/
  decl : Json
  /-- The module that defines the test, as a dotted name. -/
  module : String
  /-- A hash of the test's source, recorded with the run so an edit can invalidate it. -/
  version : String
deriving Lean.FromJson, Lean.ToJson

/-- A request for output past a known position, naming the test by its encoded declaration. -/
meta structure AwaitRequest where
  /-- The test declaration, encoded by {name}`nameToJson`. -/
  decl : Json
  /-- The number of chunks the widget already has, so only later ones are returned. -/
  since : Nat
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

/-- One reply from {lit}`awaitOutput`: any output chunks past the requested position, or the outcome. -/
meta structure AwaitResult where
  /-- The output chunks past the requested position. -/
  chunks : Array Errata.OutputChunk := #[]
  /-- The position past the returned chunks, to pass as the next request's start. -/
  nextSince : Nat := 0
  /-- When the run started, in milliseconds since the Unix epoch. -/
  startTime : Nat := 0
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

/-- Kills the runner of a name, if any, marks it finished, and forgets it. -/
private meta def dropRun (declName : Name) : IO Unit := do
  if let some state := (← runRegistry.get).get? declName then
    try (← state.kill.get) catch _ => pure ()
    state.finished.set true
    signalRun state
    runRegistry.modify (·.erase declName)

/--
Reads the runner's JSON protocol from its stdout: a {lit}`chunk` line per output fragment, then an
{lit}`outcome` line. Marks the run finished at end of input, which is reached when the process exits
or is killed, so this never holds a thread past the process's lifetime.
-/
private meta partial def readLoop (out : IO.FS.Handle) (state : RunState) : IO Unit := do
  let line ← out.getLine
  if line.isEmpty then
    state.finished.set true
    signalRun state
  else
    if let .ok j := Json.parse line then
      if let .ok c := j.getObjVal? "chunk" then
        if let .ok chunk := (fromJson? c : Except String Errata.OutputChunk) then
          state.chunks.modify (·.push chunk)
          signalRun state
      else if let .ok ex := j.getObjVal? "exec" then
        if let .ok t := (fromJson? ex : Except String Nat) then
          state.execStartTime.set t
          signalRun state
      else if let .ok o := j.getObjVal? "outcome" then
        if let .ok oc := (fromJson? o : Except String Errata.RunOutcome) then
          state.outcome.set oc
    readLoop out state

/-- The outcome shown when the build step fails, carrying its message and detail. -/
private meta def buildFailure (detail : String) : Errata.RunOutcome := {
  status := "error", durationMs := 0, message? := some "lake build failed", detail? := some detail
}

/--
Builds the test's module from the saved source, then runs the test, streaming its output into the
run state. Building first means a Run reflects the latest saved version of the test.
-/
private meta def buildAndRun (module declJson : String) (state : RunState) : IO Unit := do
  -- `lake query` builds the runner exe and the test's module (so the run reflects the saved source)
  -- and prints the exe's absolute path on stdout; progress and errors go to stderr.
  let build ← IO.Process.spawn {
    stdin := .null, stdout := .piped, stderr := .piped
    cmd := "lake", args := #["query", "errata-run-one", module]
  }
  state.kill.set build.kill
  let errTask ← IO.asTask build.stderr.readToEnd
  let queryOut ← build.stdout.readToEnd
  let buildErr := (← IO.wait errTask).toOption.getD ""
  if (← build.wait) != 0 then
    state.outcome.set (some (buildFailure buildErr))
    state.finished.set true
    signalRun state
    return
  let some runnerPath := (queryOut.splitOn "\n").find? (!·.trimAscii.isEmpty) |>.map (·.trimAscii.copy)
    | state.outcome.set (some (buildFailure "lake query did not report the runner's path"))
      state.finished.set true
      signalRun state
      return
  -- Spawn the runner directly rather than through `lake exe` so it inherits the language server's
  -- broad `LEAN_PATH`. The runner imports the arbitrary test module at runtime, which is not a
  -- dependency of the exe, so `lake exe` would narrow `LEAN_PATH` to the exe's own deps and the
  -- import would fail.
  let run ← IO.Process.spawn {
    stdin := .null, stdout := .piped, stderr := .inherit
    cmd := runnerPath, args := #[module, declJson]
  }
  state.kill.set run.kill
  state.buildMs.set ((← nowMs) - state.startTime)
  state.phase.set "running"
  signalRun state
  readLoop run.stdout state

open Server in
/-- Whether the document's live text matches what is on disk, i.e. it has no unsaved changes. -/
private meta def bufferIsClean : RequestM Bool := do
  let docMeta := (← RequestM.readDoc).meta
  let some path := System.Uri.fileUriToPath? docMeta.uri
    | return true
  match (← (IO.FS.readFile path).toBaseIO).toOption with
  | some disk => return docMeta.text.source == disk.crlfToLf
  | none => return true

open Server in
/-- Server RPC method reporting whether the file has no unsaved changes, gating the Run button. -/
@[server_rpc_method]
meta def bufferClean (_ : RunRef) : RequestM (RequestTask Bool) := do
  return RequestTask.pure (← bufferIsClean)

open Server in
/-- Server RPC method that starts running a test: builds its saved source, then streams its output. -/
@[server_rpc_method]
meta def startTest (req : StartRequest) : RequestM (RequestTask Unit) := do
  let declName ← decodeDecl req.decl
  unless ← bufferIsClean do
    throw (.mk .invalidParams "the file has unsaved changes; save it before running the test")
  dropRun declName
  let state : RunState := {
    chunks := ← IO.mkRef #[], finished := ← IO.mkRef false, outcome := ← IO.mkRef none,
    wakeup := ← IO.mkRef (← IO.Promise.new), phase := ← IO.mkRef "building", version := req.version,
    startTime := ← nowMs, buildMs := ← IO.mkRef 0, execStartTime := ← IO.mkRef 0,
    kill := ← IO.mkRef (pure ())
  }
  runRegistry.modify (·.insert declName state)
  let _ ← IO.asTask (buildAndRun req.module req.decl.compress state)
  return RequestTask.pure ()

open Server in
/-- Builds the reply for a waiter given the run's current state and the position it already has. -/
private meta def replyFrom (state : RunState) (since : Nat) : IO AwaitResult := do
  let chunks ← state.chunks.get
  let phase ← state.phase.get
  let startTime := state.startTime
  let buildMs ← state.buildMs.get
  let execStartTime ← state.execStartTime.get
  if chunks.size > since then
    let slice := chunks.extract since chunks.size
    return { chunks := slice, nextSince := since + slice.size, phase, startTime, buildMs, execStartTime }
  let done ← state.finished.get
  let outcome ← state.outcome.get
  return { nextSince := chunks.size, phase, startTime, buildMs, execStartTime, done, outcome }

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
  -- Return at once when there is new output, the run finished, or its phase changed (so a widget
  -- reconnecting mid-build learns it is building rather than waiting silently); otherwise wait.
  if chunks.size > req.since || (← state.finished.get) || (← state.phase.get) != req.phase then
    return RequestTask.pure (← replyFrom state req.since)
  RequestM.mapTaskCheap (p.resultD ()).asServerTask fun _ => liftM (replyFrom state req.since)

open Server in
/-- Server RPC method that cancels a running test by killing its process. -/
@[server_rpc_method]
meta def cancelTest (req : RunRef) : RequestM (RequestTask Unit) := do
  let declName ← decodeDecl req.decl
  dropRun declName
  return RequestTask.pure ()
