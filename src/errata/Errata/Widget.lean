/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public meta import Lean.Widget.UserWidget
public meta import Lean.Server
public meta import Errata.NameJson
public meta import Errata.WidgetOutcome

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

/--
A live (or just-finished) run. Output chunks accumulate in {name (full := RunState.chunks)}`chunks`
so a widget that reconnects after the cursor leaves and returns can replay them by index. They are
the run's one copy of its output, since the outcome's results hold none. The wakeup promise is
resolved and replaced whenever a chunk arrives or the run finishes, waking any waiter.
-/
meta structure RunState where
  /-- Every output chunk produced so far, in order. -/
  chunks : IO.Ref (Array Runner.OutputChunk)
  /--
  The reports from named results so far, in order. A named result is reported when it starts, with
  its identifier, parent, and name, and again when it finishes, with its verdict.
  -/
  results : IO.Ref (Array Runner.ResultNode)
  /-- Whether the run has finished. -/
  finished : IO.Ref Bool
  /-- The final outcome, set when the run finishes. -/
  outcome : IO.Ref (Option Runner.RunOutcome)
  /-- A promise resolved and replaced on each change, which wakes the requests waiting on the run. -/
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
  /-- The identifier that the widget gave the run when it asked for it to start. -/
  runId : String

/-- The live runs, keyed by the test's declaration name so a run survives re-elaboration. -/
meta initialize runRegistry : IO.Ref (Std.HashMap Name RunState) ← IO.mkRef {}

/--
Takes the workspace's build lock, runs {name}`act`, and releases the lock. The builds started for the
tests of one workspace then run one at a time, wherever in the workspace those tests are.

The lock is a file under the workspace's {lit}`.lake` directory, and every file worker of the
workspace opens that same file.
-/
private meta def withBuildLock (act : IO α) : IO α := do
  let dir := (← IO.currentDir) / ".lake"
  IO.FS.createDirAll dir
  let handle ← IO.FS.Handle.mk (dir / "errata-widget-build.lock") .write
  handle.lock
  try act finally handle.unlock

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
  /--
  The options for the test, in order. A name that appears more than once gives the option
  several values.
  -/
  options : Array Runner.TestOption := #[]
  /--
  An identifier the widget chose for the run, which later replies about the run carry, so the widget
  can recognize the run it asked for.
  -/
  runId : String := ""

meta instance : ToJson StartRequest where
  toJson r := Json.mkObj <|
    [("decl", r.decl), ("module", r.module), ("version", toJson r.version)] ++
    Json.opt "seed" r.seed? ++
    [("options", toJson r.options), ("runId", toJson r.runId)]

meta instance : FromJson StartRequest where
  fromJson? j := do
    return {
      decl := ← j.getObjVal? "decl"
      module := ← j.getObjVal? "module"
      version := ← j.getObjValAs? _ "version"
      seed? := ← fromJson? (j.getObjValD "seed")
      options := ← Runner.getObjValAsD j "options" #[]
      runId := ← Runner.getObjValAsD j "runId" ""
    }

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

/--
A reply from {name (scope := "Errata.Widget")}`awaitOutput`, including any output chunks past the
requested position and whether the test run has completed.
-/
meta structure AwaitResult where
  /-- The output chunks past the requested position. -/
  chunks : Array Runner.OutputChunk := #[]
  /-- The position past the returned chunks, to pass as the next request's start. -/
  nextSince : Nat := 0
  /--
  The reports from named results that are newer than those the widget already has. A named result
  is reported when it starts and again when it finishes.
  -/
  results : Array Runner.ResultNode := #[]
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
  outcome : Option Runner.RunOutcome := none
  /-- The identifier that the widget gave the run when it asked for it to start. -/
  runId : String := ""
deriving Lean.FromJson, Lean.ToJson

open Server in
/-- Decodes the declaration name from a request, failing the request if it is malformed. -/
private meta def decodeDecl (j : Json) : RequestM Name :=
  match nameOfJson? j with
  | .ok n => pure n
  | .error e => throw (.mk .invalidParams e)

/-- Resolves the run's current wakeup promise and installs a fresh one, waking any waiter. -/
private meta def signalRun (state : RunState) : IO Unit := do
  let fresh ← IO.Promise.new
  -- The protocol reader and the two forwarded streams signal a run at the same time, so each of
  -- them takes a different promise and no waiter is left on one that nothing resolves.
  let p ← state.wakeup.modifyGet fun p => (p, fresh)
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
How many finished runs stay in the registry, with the output and the outcome they collected. A
widget that is shown again loads a previous run from the registry and displays it again.
-/
private meta def finishedRunsKept : Nat := 20

/-- Forgets the finished runs beyond the number kept, oldest first. -/
private meta def forgetOldRuns : IO Unit := do
  let mut finished := #[]
  for (declName, state) in ← runRegistry.get do
    if ← state.finished.get then finished := finished.push (declName, state.startTime, state.runId)
  if finished.size ≤ finishedRunsKept then return
  let oldest := finished.qsort (fun a b => a.2.1 < b.2.1) |>.take (finished.size - finishedRunsKept)
  for (declName, startTime, runId) in oldest do
    -- A run of the same test started in the meantime takes precedence
    dropRun declName (onlyIf := fun state => state.startTime == startTime && state.runId == runId)

/-- The hash of each test's source as the {lit}`@[test]` attribute last elaborated it, by declaration. -/
meta initialize testVersions : IO.Ref (Std.HashMap Name String) ← IO.mkRef {}

/--
Records the hash of a test's current source and ends a run of the test whose source has changed
since the run started. {name}`version` is that hash, which the {lit}`@[test]` attribute passes each
time it elaborates the test, so the run of an edited test ends wherever the widget is.
-/
meta def dropRunsOfOtherVersions (declName : Name) (version : String) : IO Unit := do
  testVersions.modify (·.insert declName version)
  dropRun declName (onlyIf := (·.version != version))

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
private meta def finishWith (state : RunState) (fallback : Runner.RunOutcome) : IO Unit := do
  if (← state.finished.get) then return
  -- The outcome is in place before the run is marked finished, so a waiter that finds the run
  -- finished finds the outcome with it.
  if (← state.outcome.get).isNone then state.outcome.set (some fallback)
  -- A cancel can mark the run finished at this same moment, and only the caller that marked it
  -- wakes the waiters.
  unless ← state.finished.modifyGet fun finished => (finished, true) do
    signalRun state

/--
Handles one line of the runner's JSON protocol: an {lit}`exec` line when the test body starts, a
{lit}`chunk` line per output fragment, a {lit}`result` line as each named result starts and
finishes, and an {lit}`outcome` line at the end.
-/
private meta def handleLine (state : RunState) (line : String) : IO Unit := do
  -- A test run that has ended (e.g. a cancelled one) receives no more of the runner's reports.
  if ← state.finished.get then return
  if let .ok j := Json.parse line then
    if let .ok c := j.getObjVal? "chunk" then
      if let .ok chunk := (fromJson? c : Except String Runner.OutputChunk) then
        state.chunks.modify (·.push chunk)
        signalRun state
    else if let .ok n := j.getObjVal? "result" then
      if let .ok node := (fromJson? n : Except String Runner.ResultNode) then
        state.results.modify (·.push node)
        signalRun state
    else if let .ok ex := j.getObjVal? "exec" then
      if let .ok t := (fromJson? ex : Except String Nat) then
        state.execStartTime.set t
        signalRun state
    else if let .ok o := j.getObjVal? "outcome" then
      if let .ok oc := (fromJson? o : Except String Runner.RunOutcome) then
        state.outcome.set oc

/-- How long to wait, in milliseconds, before reading the protocol file again once it is read up. -/
private meta def protocolPollMs : UInt32 := 15

/--
Handles one line of the runner's JSON protocol. The line is provided as UTF-8 encoded bytes.

If the line is invalid UTF-8 or if it is empty, then it is skipped.
-/
private meta def handleLineBytes (state : RunState) (bytes : ByteArray) : IO Unit := do
  if let some line := String.fromUTF8? bytes then
    unless line.isEmpty do handleLine state line

/--
Handles each complete line in {name}`bytes`. Returns the bytes after the last newline, which
constitute an incomplete line, along with how many of them have been inspected for newlines. The
bytes before {name}`scanned` are assumed to not contain any newlines.
-/
private meta def handleLines (state : RunState) (bytes : ByteArray) (scanned : Nat) :
    IO (ByteArray × Nat) := do
  let mut start := 0
  for i in [scanned:bytes.size] do
    if bytes[i]! == '\n'.toUInt8 then
      handleLineBytes state (bytes.extract start i)
      start := i + 1
  -- A read that ends within a line keeps the bytes in the buffer they arrived in, so a line that
  -- spans many reads is copied when it is complete.
  if start == 0 then return (bytes, bytes.size)
  return (bytes.extract start bytes.size, bytes.size - start)

private meta structure ProtocolReaderState extends RunState where
  /-- The temporary file that the runner writes its protocol to. -/
  file : IO.FS.Handle
  /-- The runner's exit code, once it has exited. -/
  exitCode : IO (Option UInt32)
  /-- The bytes of a partially-written line of runner output. -/
  pending : ByteArray := .empty
  /--
  How many of the bytes in {name (full := ProtocolReaderState.pending)}`pending` have been looked
  at.
  -/
  scanned : Nat := 0
  /--
  Whether the runner had exited before the current read began, so that everything it wrote is
  already in the file.
  -/
  exited : Bool := false

/--
Polls the runner's protocol output file, handling each line as it is completed. Returns once the
runner has exited and the file has been read to its end. The file is read as bytes, with each line
decoded once all of it has arrived, so a read that ends within a character leaves the character
intact.
-/
private meta partial def followProtocol (reader : ProtocolReaderState) : IO Unit := do
  let bytes ← reader.file.read 65536
  if !bytes.isEmpty then
    let (pending, scanned) ← handleLines reader.toRunState (reader.pending ++ bytes) reader.scanned
    followProtocol { reader with pending, scanned }
  else if reader.exited then
    handleLineBytes reader.toRunState reader.pending
  else
    let exited := (← reader.exitCode).isSome
    unless exited do IO.sleep protocolPollMs
    followProtocol { reader with exited }

/--
Passes along what the runner writes to the output stream {name}`stream`, adding each line to the
test's own output as a chunk.

The runner's streams include the output that the test's capture misses. One example is the output of
a subprocess that the test starts. Another is an error from outside the test body, such as a failed
import, which the runner writes to standard error.
-/
private meta partial def forwardStream (stream : Runner.OutputChunk.Stream) (handle : IO.FS.Handle)
    (state : RunState) : IO Unit := do
  let line ← handle.getLine
  if line.isEmpty then return
  -- Output that arrives after the run has ended belongs to a process that outlived the runner.
  unless ← state.finished.get do
    state.chunks.modify (·.push { stream, text := line, time := ← Runner.nowMs })
    signalRun state
  forwardStream stream handle state

/--
How long to wait, in milliseconds, for the runner's output pipes to close once the runner has exited.
-/
private meta def pipeGraceMs : Nat := 500

/--
Waits until every task has finished, or until {name}`ms` milliseconds have passed. Returns whether
every task has finished.
-/
private meta def waitAtMost (ms : Nat) (tasks : List (Task (Except IO.Error Unit))) : IO Bool := do
  let allDone ← IO.mapTasks (fun _ => pure ()) tasks
  let timeout ← IO.asTask (prio := .dedicated) (IO.sleep ms.toUInt32)
  discard <| IO.waitAny [allDone, timeout]
  IO.hasFinished allDone

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
private meta def buildFailure (detail : String) : Runner.RunOutcome := {
  status := .error, durationMs := 0, message? := some "lake build failed"
  detail? := some (endOf detail)
}

/-- The outcome shown when building or running the test raises an error, such as a failed spawn. -/
private meta def launchFailure (e : IO.Error) : Runner.RunOutcome := {
  status := .error, durationMs := 0, message? := some s!"the test could not be run: {e}"
}

/--
The error outcome for a runner that exited with code {name}`code` before reporting an outcome of its
own. The reason for the failure is usually in what the runner wrote to standard error, which the
widget shows as part of the test's output.
-/
private meta def runnerFailure (code : UInt32) : Runner.RunOutcome := {
  status := .error, durationMs := 0
  message? := some s!"the test runner exited with code {code} before reporting an outcome"
}

/--
Builds the module in {name}`source` and the runner, then runs the test and streams its output into
{name}`state`. The runner imports the test's module's {lit}`.olean`, so it must first be built. The
module and the declaration are encoded by {name}`nameToJson`, and the options are a JSON array of
{name}`Runner.TestOption`s.
-/
private meta def buildAndRun (source : System.FilePath) (moduleJson declJson optionsJson : String)
    (seed? : Option Nat) (state : RunState) : IO Unit := do
  -- The language server's Lake sets `LAKE` to its own path.
  let lake := (← IO.getEnv "LAKE").getD "lake"
  let (buildErr, queryOut, buildCode) ← withBuildLock do
    if ← state.finished.get then return ("", "", 0)
    -- `lake query` builds the runner and the module, then prints the runner's path. Its own process
    -- group lets a cancel kill the compilers that Lake starts.
    let build ← IO.Process.spawn {
      stdin := .null, stdout := .piped, stderr := .piped, setsid := true
      cmd := lake, args := #["query", "errata-run-one", source.toString]
    }
    unless ← setKill state build.kill do
      let _ ← build.wait
      return ("", "", 0)
    let errTask ← IO.asTask (prio := .dedicated) build.stderr.readToEnd
    let queryOut ← build.stdout.readToEnd
    let buildErr := (← IO.wait errTask).toOption.getD ""
    let buildCode ← build.wait
    -- The build's process group id is free for reuse once `wait` returns, so a cancel must no longer
    -- kill that group.
    state.kill.set (pure ())
    return (buildErr, queryOut, buildCode)
  if ← state.finished.get then return
  if buildCode != 0 then
    finishWith state (buildFailure buildErr)
    return
  let some runnerPath := (queryOut.splitOn "\n").find? (!·.trimAscii.isEmpty) |>.map (·.trimAscii.copy)
    | finishWith state (buildFailure "lake query did not report the runner's path")
      return
  -- The runner writes its protocol to a file of its own, where no other output can mix into it.
  IO.FS.withTempFile fun _ protocolPath => do
    let protocol ← IO.FS.Handle.mk protocolPath .read
    -- The runner finds the test's module through the `LEAN_PATH` that it inherits. It exits when its
    -- standard input closes, which happens when this file worker exits. Its own process group lets a
    -- cancel kill the processes that the test starts.
    let run ← IO.Process.spawn {
      stdin := .piped, stdout := .piped, stderr := .piped, setsid := true
      cmd := runnerPath
      args := #[protocolPath.toString, moduleJson, declJson, optionsJson]
        ++ (seed?.map (#[toString ·])).getD #[]
    }
    unless ← setKill state run.kill do
      let _ ← run.wait
      return
    state.buildMs.set ((← Runner.nowMs) - state.startTime)
    state.phase.set "running"
    signalRun state
    let runErrTask ← IO.asTask (prio := .dedicated) (forwardStream .stderr run.stderr state)
    let runOutTask ← IO.asTask (prio := .dedicated) (forwardStream .stdout run.stdout state)
    -- The exit code, recorded when the runner is found to have exited.
    let code ← IO.mkRef none
    let exitCode : IO (Option UInt32) := do
      if let some c ← code.get then return some c
      let c? ← run.tryWait
      if c?.isSome then
        -- The runner's process group id is free for reuse once `tryWait` reports the exit, so a
        -- cancel must no longer kill that group.
        state.kill.set (pure ())
      code.set c?
      return c?
    followProtocol { state with file := protocol, exitCode }
    -- Processes that the test started can hold the runner's output pipes open after the runner has
    -- exited. They get a grace period, then are killed, and what they wrote is still read.
    unless ← waitAtMost pipeGraceMs [runOutTask, runErrTask] do
      try run.kill catch _ => pure ()
      discard <| waitAtMost pipeGraceMs [runOutTask, runErrTask]
    -- `followProtocol` returns only after the runner has exited, so the code is set.
    let code := (← code.get).getD 0
    finishWith state (runnerFailure code)

/--
A mapping from LSP document URIs to the saved LSP version and hash for the document.

This is used to avoid repeatedly re-hashing the same document while checking whether the file has
been edited in order to update widget states.
-/
meta initialize documentHashes : IO.Ref (Std.HashMap String (Nat × UInt64)) ← IO.mkRef {}

/-- The hash of a file's text on disk, with the file's metadata when it was read. -/
private meta structure DiskHash where
  /-- The file's modification time when it was read. -/
  modified : IO.FS.SystemTime
  /-- The file's size in bytes when it was read. -/
  size : UInt64
  /-- The hash of the file's text, with line endings normalized. -/
  hash : UInt64

/--
A mapping from test filenames on disk to cached hashes of their text.

When modification time and size match, the hash does not need to be recomputed.
-/
private meta initialize diskHashes : IO.Ref (Std.HashMap String DiskHash) ← IO.mkRef {}

open Server in
/--
The hash of the document's live text, computed once for each version of the document.
-/
private meta def documentHash : RequestM UInt64 := do
  let docMeta := (← RequestM.readDoc).meta
  if let some (version, hash) := (← documentHashes.get).get? docMeta.uri then
    if version == docMeta.version then return hash
  -- The language server normalizes line endings, so there's no need to do so here
  let hash := docMeta.text.source.hash
  documentHashes.modify (·.insert docMeta.uri (docMeta.version, hash))
  return hash

/--
The hash of a file's text on disk, for comparison to {name}`documentHash`. The file is read again
only when its modification time or size has changed.
-/
private meta def diskHash (path : System.FilePath) : IO (Option UInt64) := do
  let metadata ←
    try path.metadata
    catch _ => return none
  if let some cached := (← diskHashes.get).get? path.toString then
    if cached.modified == metadata.modified && cached.size == metadata.byteSize then
      return some cached.hash
  let text ←
    try IO.FS.readFile path
    catch _ => return none
  let hash := text.crlfToLf.hash
  diskHashes.modify
    (·.insert path.toString { modified := metadata.modified, size := metadata.byteSize, hash })
  return some hash

open Server in
/-- Whether the document's live text matches what is on disk, i.e. it has no unsaved changes. -/
private meta def bufferIsClean : RequestM Bool := do
  let some path := System.Uri.fileUriToPath? (← RequestM.readDoc).meta.uri
    | return true
  match ← diskHash path with
  | some disk => return (← documentHash) == disk
  -- A document that does not exist on disk is certainly unsaved
  | none => return false

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
  let hash ← documentHash
  let changedSinceRun := match (← runRegistry.get).get? declName with
    | some state => state.sourceHash != hash
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
  let options := toJson req.options |>.compress
  let _ ← decodeDecl req.module
  let some source := System.Uri.fileUriToPath? (← RequestM.readDoc).meta.uri
    | throw (.mk .invalidParams "the test's document is not a file")
  unless ← bufferIsClean do
    throw (.mk .invalidParams "the file has unsaved changes; save it before running the test")
  -- The request includes the hash of the test's source from when the widget was shown. A hash
  -- mismatch means that the widget's state is out of date.
  if let some current := (← testVersions.get).get? declName then
    unless current == req.version do
      throw (.mk .invalidParams "the test has changed since the widget was shown; try again")
  let state : RunState := {
    chunks := ← IO.mkRef #[], results := ← IO.mkRef #[],
    finished := ← IO.mkRef false, outcome := ← IO.mkRef none,
    wakeup := ← IO.mkRef (← IO.Promise.new), phase := ← IO.mkRef "building", version := req.version,
    startTime := ← Runner.nowMs, buildMs := ← IO.mkRef 0, execStartTime := ← IO.mkRef 0,
    kill := ← IO.mkRef (pure ()), sourceHash := ← documentHash, runId := req.runId
  }
  -- The new run replaces the previous one in the same step that finds it.
  let previous? ← runRegistry.modifyGet fun runs => (runs.get? declName, runs.insert declName state)
  if let some previous := previous? then stopRun previous
  forgetOldRuns
  -- The task spends most of its time blocked on the build and the runner, so it has its own thread.
  let _ ← IO.asTask (prio := .dedicated) do
    try buildAndRun source req.module.compress req.decl.compress options seed? state
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
  let (chunks, nextSince) ← state.chunks.modifyGet fun all =>
    ((all.extract since all.size, all.size), all)
  let phase ← state.phase.get
  let startTime := state.startTime
  let elapsedMs := (← Runner.nowMs) - startTime
  let buildMs ← state.buildMs.get
  let execStartTime ← state.execStartTime.get
  let (results, nextSinceResults) ← state.results.modifyGet fun all =>
    ((all.extract sinceResults all.size, all.size), all)
  return {
    chunks, nextSince, results, nextSinceResults, runId := state.runId
    phase, startTime, elapsedMs, buildMs, execStartTime, done, outcome
  }

open Server in
/--
Server RPC method that returns output chunks past {name (full := AwaitRequest.since)}`since`, or the
final outcome. When nothing new is available yet, the reply waits on the run's wakeup promise, which
the run resolves when something changes. A reconnecting widget replays from {lit}`since := 0`.
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
  let chunkCount ← state.chunks.modifyGet fun all => (all.size, all)
  let resultCount ← state.results.modifyGet fun all => (all.size, all)
  -- Return at once when there is new output, a named result has started or finished, the run
  -- finished, or its phase changed, so that a widget reconnecting mid-build learns that the run is
  -- building; otherwise wait.
  if chunkCount > req.since || resultCount > req.sinceResults || (← state.finished.get) ||
      (← state.phase.get) != req.phase then
    return RequestTask.pure (← replyFrom state req.since req.sinceResults)
  RequestM.mapTaskCheap (p.resultD ()).asServerTask fun _ =>
    liftM (replyFrom state req.since req.sinceResults)

/-- A request to cancel the run of a test. -/
meta structure CancelRequest where
  /-- The test declaration, encoded by {name}`nameToJson`. -/
  decl : Json
  /--
  The identifier of the run to cancel, as the widget gave it when it asked for the run to start.
  When it is empty, the request names whichever run of the test the server holds.
  -/
  runId : String := ""

meta instance : ToJson CancelRequest where
  toJson r := Json.mkObj [("decl", r.decl), ("runId", toJson r.runId)]

meta instance : FromJson CancelRequest where
  fromJson? j := do
    return {
      decl := ← j.getObjVal? "decl"
      runId := ← Runner.getObjValAsD j "runId" ""
    }

/-- The reply to a request to cancel a run. -/
meta structure CancelResult where
  /-- Whether the run named by the request was in fact terminated by the request. -/
  cancelled : Bool
deriving Lean.FromJson, Lean.ToJson

open Server in
/--
Server RPC method that cancels a run of a test by killing its process. The request uses the run
identifier that the widget gave it, so a newer run of the same test keeps going. A run that has
already finished keeps its outcome. The reply says whether the run was cancelled.
-/
@[server_rpc_method]
meta def cancelTest (req : CancelRequest) : RequestM (RequestTask CancelResult) := do
  let declName ← decodeDecl req.decl
  let runId := req.runId
  let some state := (← runRegistry.get).get? declName
    | return RequestTask.pure ({ cancelled := false } : CancelResult)
  unless runId.isEmpty || state.runId == runId do
    return RequestTask.pure ({ cancelled := false } : CancelResult)
  -- Two cancels of one run can arrive together, and the run can finish on its own at that moment,
  -- so exactly one of them reports the cancel.
  if ← state.finished.modifyGet fun finished => (finished, true) then
    return RequestTask.pure ({ cancelled := false } : CancelResult)
  try (← state.kill.get) catch _ => pure ()
  signalRun state
  return RequestTask.pure ({ cancelled := true } : CancelResult)
