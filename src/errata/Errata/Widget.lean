/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public meta import Lean.Widget.UserWidget
public meta import Lean.Server
public meta import Errata.NameJson
public meta import Errata.WidgetState
public meta import Errata.ProcessControl
public meta import Errata.RunnerConfig
public meta import Errata.WidgetWorkspace

public section

set_option linter.missingDocs true
set_option doc.verso true

open Lean

namespace Errata.Widget

/--
Shown when the text cursor is on a test's source span. It offers a "run" button that runs the test
through the Errata driver, streaming its output as it is produced.
-/
@[widget_module]
meta def runTestWidget : Lean.Widget.Module where
  javascript := include_str "widget/run_test_widget.js"

/-- A setting that a test takes, which the widget offers a field for. -/
meta structure DeclaredSetting where
  /-- The setting's name: its fully qualified declaration name. -/
  name : String
  /-- Whether the test runs without a value for the setting. -/
  optional : Bool
  /-- The setting's docstring. -/
  description? : Option String := none
  /-- The setting's declared default. -/
  default? : Option String := none
deriving Lean.FromJson, Lean.ToJson

/-- What the server knows of a test from the latest elaboration of its source. -/
meta structure TestNote where
  /-- A hash of the test's source. -/
  version : String
  /-- The test's own declaration, where a failure with no more specific place is reported. -/
  location? : Option Location := none
  /-- The settings that the test takes, in the order of its parameters. -/
  settings : Array DeclaredSetting := #[]
  /-- The module that defines the test. -/
  module : Name := .anonymous
  /-- The test's source file, as its test executable lists it. -/
  file : String := ""
  /-- The test's tags. -/
  tags : Array String := #[]

/-- The live and finished runs, keyed by the test's declaration so a run survives re-elaboration. -/
meta initialize runRegistry : IO.Ref (Std.HashMap Name RunState) ← IO.mkRef {}

/-- What the latest elaboration of each test recorded, by declaration. -/
meta initialize testNotes : IO.Ref (Std.HashMap Name TestNote) ← IO.mkRef {}

/--
Takes the workspace's build lock, and runs {name}`act` with an action that releases it; the lock is
released when {name}`act` ends, if {name}`act` has not released it earlier. The runs started for the
tests of one workspace then build one at a time, wherever in the workspace those tests are, since
each builds in the workspace and writes the driver's configuration files.

The lock is a file under the workspace's {lit}`.lake` directory, and every file worker of the
workspace opens that same file.
-/
private meta def withBuildLock (act : IO Unit → IO α) : IO α := do
  let dir := (← IO.currentDir) / ".lake"
  IO.FS.createDirAll dir
  let handle ← IO.FS.Handle.mk (dir / "errata-widget-build.lock") .write
  handle.lock
  let held ← IO.mkRef true
  let release : IO Unit := do
    if ← held.modifyGet fun h => (h, false) then handle.unlock
  try act release finally release

/--
A request to start running a test: the declaration and the module that defines it, the values the
run gives the test, and the identifier of the run.
-/
meta structure StartRequest where
  /-- The test declaration to run, encoded by {name}`nameToJson`. -/
  decl : Json
  /-- The module that defines the test, encoded by {name}`nameToJson`. -/
  module : Json
  /-- A hash of the test's source, recorded with the run so an edit can invalidate it. -/
  version : String
  /--
  The seed for property tests, or {lean}`none` to have the runner choose one. Because JavaScript
  represents JSON numbers as floats, cutting off their range, it is a string of decimal digits.
  -/
  seed? : Option String := none
  /-- Values for the test's settings, which the run passes to the driver with {lit}`--set`. -/
  settings : Array SettingValue := #[]
  /-- The profile of the run, which the run passes to the driver with {lit}`-P`, if any. -/
  profile? : Option String := none
  /--
  The identifier that the widget chose for the run, which later replies about the run include, so
  the widget can recognize the run it asked for.
  -/
  runId : String

meta instance : ToJson StartRequest where
  toJson r := Json.mkObj <|
    [("decl", r.decl), ("module", r.module), ("version", toJson r.version)] ++
    Json.opt "seed" r.seed? ++ Json.opt "profile" r.profile? ++
    [("settings", toJson r.settings), ("runId", toJson r.runId)]

/--
The {lit}`settings` field may be absent, and every other field but {lit}`seed` and {lit}`profile` is
required.
-/
meta instance : FromJson StartRequest where
  fromJson? j := do
    return {
      decl := ← j.getObjVal? "decl"
      module := ← j.getObjVal? "module"
      version := ← j.getObjValAs? _ "version"
      seed? := ← fromJson? (j.getObjValD "seed")
      settings := ← match j.getObjVal? "settings" with
        | .ok v => fromJson? v
        | .error _ => pure #[]
      profile? := ← fromJson? (j.getObjValD "profile")
      runId := ← j.getObjValAs? _ "runId"
    }

/-- A request for output past a known position, naming the test by its encoded declaration. -/
meta structure AwaitRequest where
  /-- The test declaration, encoded by {name}`nameToJson`. -/
  decl : Json
  /-- The number of chunks the widget already has, so only later ones are returned. -/
  since : Nat
  /--
  The number of reports from results that the widget already has, counted the same way as
  {name (full := AwaitRequest.since)}`since`.
  -/
  sinceResults : Nat := 0
  /-- The test's source hash; a run recorded under a different one is stale and ignored. -/
  version : String
  /-- The phase the widget last saw; a reply is returned at once when the run's phase differs. -/
  phase : String
deriving Lean.FromJson, Lean.ToJson

/-- A request that names a test by its declaration, encoded by {name}`nameToJson`. -/
meta structure RunRef where
  /-- The test declaration, encoded by {name}`nameToJson`. -/
  decl : Json
deriving Lean.FromJson, Lean.ToJson

/--
A reply from {name (scope := "Errata.Widget")}`awaitOutput`: the output chunks and result reports
past the requested positions, and the run's phase and timings, with its outcome once it has one.
-/
meta structure AwaitResult where
  /-- The output chunks past the requested position. -/
  chunks : Array OutputChunk := #[]
  /-- The position past the returned chunks, to pass as the next request's start. -/
  nextSince : Nat := 0
  /--
  The reports from results that are newer than those the widget already has. A named result is
  reported when it starts and again when it finishes, and the test's own result when the test ends.
  -/
  results : Array ResultNode := #[]
  /--
  How many reports from results the run has made so far. The widget sends this back with its next
  request, as the number of reports it already has.
  -/
  nextSinceResults : Nat := 0
  /-- The fixture phases that ran for the test so far. -/
  steps : Array Step := #[]
  /-- The run-level issues that the runner reported so far. -/
  issues : Array Issue := #[]
  /-- When the run started, in milliseconds since the Unix epoch. -/
  startTime : Nat := 0
  /--
  How long ago the run started, in milliseconds by the server's clock. The widget's elapsed counter
  ticks from it, so the display stays right when the server's clock differs from the editor's.
  -/
  elapsedMs : Nat := 0
  /-- How long the driver took before the runner began, in milliseconds; 0 while building. -/
  buildMs : Nat := 0
  /-- When the test body started, in epoch ms; 0 until then. Output offsets are relative to it. -/
  execStartTime : Nat := 0
  /--
  The run's phase: {lit}`waiting` for the build lock, {lit}`building`, {lit}`running`,
  {lit}`done`, or {lit}`cancelled`.
  -/
  phase : String := "running"
  /-- Whether the run is over and no more output will arrive. -/
  done : Bool := false
  /-- The outcome, present once a run is done; a cancelled run has none. -/
  outcome : Option RunOutcome := none
  /-- The identifier that the widget gave the run when it asked for it to start. -/
  runId : String := ""
deriving Lean.FromJson, Lean.ToJson

open Server in
/-- Decodes the declaration name from a request, failing the request if it is malformed. -/
private meta def decodeDecl (j : Json) : RequestM Name :=
  match nameOfJson? j with
  | .ok n => pure n
  | .error e => throw (.mk .invalidParams e)

/--
Forgets the run of a name, if any, and cancels it. The run is taken out of the registry in the same
step that finds it, so a run that a concurrent request has just started stays in place.
{name}`onlyIf` picks which runs are dropped.
-/
private meta def dropRun (declName : Name) (onlyIf : RunState → Bool := fun _ => true) :
    IO Unit := do
  let taken ← runRegistry.modifyGet fun runs =>
    match runs.get? declName with
    | some state => if onlyIf state then (some state, runs.erase declName) else (none, runs)
    | none => (none, runs)
  if let some state := taken then discard <| state.apply .cancel

/--
How many finished runs stay in the registry, with the output and the outcome they collected. A
widget that is shown again loads a previous run from the registry and displays it again.
-/
private meta def finishedRunsKept : Nat := 20

/-- Forgets the finished runs beyond the number kept, oldest first. -/
private meta def forgetOldRuns : IO Unit := do
  let mut finished := #[]
  for (declName, state) in ← runRegistry.get do
    unless (← state.phase).isLive do finished := finished.push (declName, state)
  if finished.size ≤ finishedRunsKept then return
  let oldest := finished.qsort (fun a b => a.2.startTime < b.2.startTime)
    |>.take (finished.size - finishedRunsKept)
  for (declName, old) in oldest do
    -- A run of the same test started in the meantime takes precedence
    dropRun declName
      (onlyIf := fun state => state.startTime == old.startTime && state.runId == old.runId)

/--
Records what the latest elaboration of a test found, and ends a run of the test whose source has
changed since the run started. The {lit}`@[test]` attribute calls it each time it elaborates the
test, so the run of an edited test ends wherever the widget is.
-/
meta def noteTest (declName : Name) (note : TestNote) : IO Unit := do
  testNotes.modify (·.insert declName note)
  dropRun declName (onlyIf := (·.version != note.version))

/-- The number of characters from the end of the driver's output that a failed run reports. -/
private meta def detailLimit : Nat := 4000

/--
The end of a process's output, which is where it says what went wrong: its last
{name}`detailLimit` characters. A build that fails after a long log then sends the widget a reply of
a few kilobytes.
-/
private meta def endOf (text : String) : String :=
  if text.length ≤ detailLimit then text
  else "…\n" ++ text.drop (text.length - detailLimit)

/--
The outcome of a driver that ended before the runner began, such as one whose build failed or whose
script Lake could not find, with the end of its output.
-/
private meta def buildFailure (output : String) : RunOutcome := {
  status := "error", message? := some "the build ended before the test ran"
  detail? := some (endOf output)
}

/-- The outcome when starting or following the driver raises an error, such as a failed spawn. -/
private meta def launchFailure (e : IO.Error) : RunOutcome :=
  { status := "error", message? := some s!"the test could not be run: {e}" }

/--
The outcome of a driver that exited with code {name}`code` after the runner began and before the
runner ended the run, with the end of the driver's output.
-/
private meta def runnerFailure (code : UInt32) (output : String) : RunOutcome := {
  status := "error"
  message? := some s!"the test runner exited with code {code} before reporting an outcome"
  detail? := some (endOf output)
}

/-- The name of the setting that holds the seed for property tests. -/
private meta def seedSetting : String := Runner.seedSetting

/--
How long to wait, in milliseconds, for the driver's output pipes to close once the driver has
exited.
-/
private meta def pipeGraceMs : Nat := 500

/-- How much of the driver's output is kept as it arrives, in characters. -/
private meta def outputKept : Nat := 64000

/--
Runs the test through the driver and applies the changes that the runner's events make to
{name}`state`. The run waits for the workspace's build lock and holds it until the runner begins its
Run phase, by which time the driver has built the test's module and written its configuration, so
another run in the workspace builds while this one's test runs. The run's kill ends the driver's
process group. The driver's standard input is a lifeline that this process holds, and
{lit}`ERRATA_DRIVER_LIFELINE` asks the driver to hand it on to the runner, so the runner and the
tests end when this process does. What the driver writes, Lake's build log and the runner's report,
is kept for the message of a driver that fails before the runner ends the run. {name}`own?` is the
test's own declaration, as {name}`RunOutcome.ofRecord` uses it.
-/
private meta def runThroughDriver (state : RunState) (request : DriverRequest)
    (own? : Option Location) : IO Unit := do
  -- The language server's Lake sets `LAKE` to its own path.
  let lake := (← IO.getEnv "LAKE").getD "lake"
  withBuildLock fun releaseLock => do
    -- A run cancelled while it waited for the lock has nothing more to do.
    unless ← state.apply (.locked (← Protocol.nowMs)) do return
    IO.FS.withTempFile fun _ eventsPath => do
      let events ← ProcessControl.Tail.open eventsPath
      let driver ← IO.Process.spawn {
        stdin := .piped, stdout := .piped, stderr := .piped, setsid := true
        env := #[("ERRATA_DRIVER_LIFELINE", some "1")]
        cmd := lake, args := driverArgs { request with eventsPath }
      }
      -- A run cancelled while the driver started has nothing to arm, so the driver ends here.
      unless ← state.apply (.arm driver.kill) do
        try driver.kill catch _ => pure ()
        discard driver.wait
        return
      let output ← IO.mkRef ""
      let keep (line : String) : IO Unit := output.modify fun text =>
        let text := text ++ line
        if text.length ≤ outputKept then text else text.drop (text.length - outputKept) |>.copy
      let forward (h : IO.FS.Handle) := ProcessControl.forwardLines h keep
      let outTask ← IO.asTask (prio := .dedicated) (forward driver.stdout)
      let errTask ← IO.asTask (prio := .dedicated) (forward driver.stderr)
      -- The exit code, recorded when the driver is found to have exited.
      let code ← IO.mkRef none
      let exited : IO Bool := do
        if (← code.get).isSome then return true
        let c? ← driver.tryWait
        -- The driver's process group id is free for reuse once `tryWait` reports the exit, and
        -- the rest of the events file then decides the outcome, so a cancel no longer applies.
        if c?.isSome then discard <| state.apply .exited
        code.set c?
        return c?.isSome
      let cache ← SourceLines.new
      events.follow exited fun bytes => do
        let line := ProcessControl.decodeLine bytes
        for change in ← changesOfLine cache request.test (← Protocol.nowMs) own? line do
          discard <| state.apply change
        if beginsRunPhase line then releaseLock
      -- Processes that outlived the driver can hold its output pipes open. They get a grace period,
      -- and what they wrote before it ends is kept.
      discard <| ProcessControl.waitAtMost pipeGraceMs [outTask, errTask]
      -- `Tail.follow` returns only after the driver has exited, so the code is set.
      let code := (← code.get).getD 0
      let text ← output.get
      let fallback :=
        if (← state.phase) matches .building then buildFailure text
        else runnerFailure code text
      discard <| state.apply (.finish fallback)

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

/-- A field for one of a test's settings, as the widget shows it. -/
meta structure SettingField where
  /-- The setting's name. -/
  name : String
  /-- Whether the test runs without a value for the setting. -/
  optional : Bool
  /-- The setting's docstring. -/
  description? : Option String := none
  /-- The setting's declared default. -/
  default? : Option String := none
  /-- The value that the profile gives the setting, which fills the field at first. -/
  profileValue? : Option String := none
  /--
  The Lake target whose result the profile gives the setting, as {lit}`{ needs = … }` names it;
  the driver builds it when the test runs.
  -/
  needs? : Option String := none
deriving Lean.FromJson, Lean.ToJson

/-- A profile that the widget offers for a test's runs, with a field for each of its settings. -/
meta structure ProfileOption where
  /-- The profile's name. -/
  name : String
  /--
  Whether the profile's default filter leaves the test out, so that a run under it sets the default
  filter aside. Only the {lit}`default` profile is offered so, when no profile selects the test.
  -/
  fallback : Bool := false
  /-- A field for each setting that the test takes, other than the seed, with the profile's values. -/
  fields : Array SettingField
deriving Lean.FromJson, Lean.ToJson

/-- The reply to a request for a test's settings. -/
meta structure SettingsReply where
  /--
  The profile whose values fill the fields at first: {lit}`default` when it is offered, and
  otherwise the first profile offered.
  -/
  profile : String
  /-- A field for each setting that the test takes, other than the seed, in parameter order. -/
  fields : Array SettingField
  /--
  The profiles offered for the test's runs, as {name}`profileChoices` orders them. There are none
  until the driver has elaborated the workspace's configuration, and runs then use the default
  profile.
  -/
  profiles : Array ProfileOption := #[]
deriving Lean.FromJson, Lean.ToJson

/-- The directory where the driver writes the configuration that it elaborates. -/
private meta def configurationDir : IO System.FilePath :=
  return (← IO.currentDir) / ".lake" / "errata"

/--
The configuration that the driver last elaborated in the workspace's {lit}`.lake/errata`, with the
modules of the root package's libraries, or {lean}`none` when it has written none.
-/
private meta def lastConfiguration : IO (Option (Runner.Config × Array LibraryModules)) := do
  let dir ← configurationDir
  try
    let config ← Runner.Config.load (dir / "config.json") (dir / "workspace.json")
    let workspace ← Runner.readJsonFile (dir / "workspace.json")
    return some (config, LibraryModules.ofWorkspaceJson workspace)
  catch _ => return none

/--
The settings to which the profile named {name}`profile` gives the result of a Lake target, with the
target, from the configuration that the driver last elaborated, or none when it has written none.
-/
private meta def profileNeeds (profile : String) : IO (Array (String × String)) := do
  try
    let config ← Runner.readJsonFile ((← configurationDir) / "config.json")
    let settings := (config.getObjValD "profiles").getObjValD profile |>.getObjValD "settings"
    let .ok fields := settings.getObj? | return #[]
    return fields.toArray.filterMap fun (k, v) =>
      (v.getObjValAs? String "needs").toOption.map (k, ·)
  catch _ => return #[]

/--
The test as a filter sees it: its name, file, and tags, and the test executable of the library that
{name}`libraries` says holds its module, or the empty name when none does.
-/
private meta def testRecord (declName : Name) (note : TestNote)
    (libraries : Array LibraryModules) : Filter.Record :=
  { name := (privateToUserName declName).toString, file := note.file
    exe := (libraryOf libraries note.module).getD "", tags := note.tags }

/--
The profiles that the widget offers for runs of the test {name}`declName`, from the configuration
that the driver last elaborated, or none when it has written none.
-/
private meta def profileChoicesOf (declName : Name) : IO (Array ProfileChoice) := do
  let some note := (← testNotes.get).get? declName | return #[]
  let some (config, libraries) ← lastConfiguration | return #[]
  return profileChoices config (testRecord declName note libraries)

/--
The fields for the settings {name}`declared`, other than the seed, with the values that a profile
gives them and the targets whose results it gives them.
-/
private meta def fieldsOf (declared : Array DeclaredSetting)
    (values needs : Array (String × String)) : Array SettingField :=
  declared.filter (·.name != seedSetting) |>.map fun s => {
    name := s.name, optional := s.optional, description? := s.description?, default? := s.default?
    profileValue? := (values.findRev? (·.1 == s.name)).map (·.2)
    needs? := (needs.find? (·.1 == s.name)).map (·.2)
  }

open Server in
/--
Server RPC method that gives the fields for a test's settings and the profiles that its runs can
use. The profiles offered are those whose default filters select the test, or the {lit}`default`
profile as the fallback when none does. For each profile and each setting that the test takes, other than
the seed, a field gives the setting's name, description, and declared default, whether it is
optional, and the value that the test receives from the profile, which is the first matching
override's or else the profile's own, or the target whose result the profile gives it.
-/
@[server_rpc_method]
meta def testSettings (req : RunRef) : RequestM (RequestTask SettingsReply) := do
  let declName ← decodeDecl req.decl
  let declared := (((← testNotes.get).get? declName).map (·.settings)).getD #[]
  let profiles ← (← profileChoicesOf declName).mapM fun c => do
    return { name := c.name, fallback := c.fallback
             fields := fieldsOf declared c.values (← profileNeeds c.name) : ProfileOption }
  let first? := profiles.find? (·.name == "default") <|> profiles[0]?
  return RequestTask.pure {
    profile := (first?.map (·.name)).getD "default"
    fields := (first?.map (·.fields)).getD (fieldsOf declared #[] #[])
    profiles }

open Server in
/--
Server RPC method that starts running a test: the driver builds its saved source and runs it, and
the run's output streams in. The driver is the script of the package whose directory holds the
{lit}`Errata` modules on the search path, and the run uses the profile that the request names.
-/
@[server_rpc_method]
meta def startTest (req : StartRequest) : RequestM (RequestTask Unit) := do
  let declName ← decodeDecl req.decl
  let module ← decodeDecl req.module
  if req.runId.isEmpty then
    throw (.mk .invalidParams "a run needs an identifier")
  let seed? ← req.seed?.mapM fun s =>
    match s.toNat? with
    | some seed => pure seed
    | none =>
      throw (.mk .invalidParams s!"the seed must be a natural number in decimal digits: {s}")
  unless ← bufferIsClean do
    throw (.mk .invalidParams "the file has unsaved changes; save it before running the test")
  -- The request includes the hash of the test's source from when the widget was shown. A hash
  -- mismatch means that the widget's state is out of date.
  let note? := (← testNotes.get).get? declName
  if let some note := note? then
    unless note.version == req.version do
      throw (.mk .invalidParams "the test has changed since the widget was shown; try again")
  let state ← RunState.new req.runId req.version (← Protocol.nowMs) (← documentHash)
  -- The new run replaces the previous one in the same step that finds it.
  let previous? ← runRegistry.modifyGet fun runs => (runs.get? declName, runs.insert declName state)
  if let some previous := previous? then discard <| previous.apply .cancel
  forgetOldRuns
  let leanPath := System.SearchPath.parse ((← IO.getEnv "LEAN_PATH").getD "") ++
    (← searchPathRef.get)
  -- A profile that leaves the test out is offered only as the fallback, whose runs set the default
  -- filter aside.
  let ignoreDefaultFilter ← match req.profile? with
    | some p => pure <| (← profileChoicesOf declName).any (fun c => c.name == p && c.fallback)
    | none => pure false
  let request : DriverRequest := {
    module, test := (privateToUserName declName).toString, seed?
    takesSeed := note?.any (·.settings.any (·.name == seedSetting))
    settings := req.settings.map fun s => (s.name, s.value)
    script := ← driverScript leanPath (← IO.currentDir)
    profile? := req.profile?, ignoreDefaultFilter
  }
  -- The task spends most of its time blocked on the driver, so it has its own thread.
  let _ ← IO.asTask (prio := .dedicated) do
    try runThroughDriver state request (note?.bind (·.location?))
    catch e => discard <| state.apply (.finish (launchFailure e))
  return RequestTask.pure ()

/--
The reply for a waiter, from the run's data at one moment and the positions the waiter already has.
The chunks past those positions come together with the run's phase, so a widget that reconnects to a
finished run settles in a single reply.
-/
private meta def replyFrom (state : RunState) (d : RunData) (since sinceResults : Nat) :
    IO AwaitResult := do
  return {
    chunks := d.chunks.extract since d.chunks.size, nextSince := d.chunks.size
    results := d.results.extract sinceResults d.results.size, nextSinceResults := d.results.size
    steps := d.steps, issues := d.issues, runId := state.runId, phase := d.phase.name
    startTime := state.startTime, elapsedMs := (← Protocol.nowMs) - state.startTime
    buildMs := d.buildMs, execStartTime := d.execStartTime
    done := !d.phase.isLive
    outcome := match d.phase with
      | .done o => some o
      | _ => none
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
  let d ← state.data.get
  -- Return at once when there is new output, a result has reported, the run is over, or its phase
  -- changed, so that a widget reconnecting mid-build learns that the run is building; otherwise
  -- wait for the next change.
  if d.chunks.size > req.since || d.results.size > req.sinceResults || !d.phase.isLive ||
      d.phase.name != req.phase then
    return RequestTask.pure (← replyFrom state d req.since req.sinceResults)
  RequestM.mapTaskCheap (d.wakeup.resultD ()).asServerTask fun _ =>
    liftM do replyFrom state (← state.data.get) req.since req.sinceResults

/-- A request to cancel the run of a test. -/
meta structure CancelRequest where
  /-- The test declaration, encoded by {name}`nameToJson`. -/
  decl : Json
  /-- The identifier of the run to cancel, which the widget gave the run when it started it. -/
  runId : String
deriving Lean.FromJson, Lean.ToJson

/-- The reply to a request to cancel a run. -/
meta structure CancelResult where
  /-- Whether the run named by the request was in fact cancelled by the request. -/
  cancelled : Bool
deriving Lean.FromJson, Lean.ToJson

open Server in
/--
Server RPC method that cancels a run of a test by killing the driver's process group. The request
names the run by the identifier that the widget gave it, so a newer run of the same test keeps
going. A run that is over keeps its outcome. The reply says whether the run was cancelled.
-/
@[server_rpc_method]
meta def cancelTest (req : CancelRequest) : RequestM (RequestTask CancelResult) := do
  let declName ← decodeDecl req.decl
  let some state := (← runRegistry.get).get? declName
    | return RequestTask.pure ({ cancelled := false } : CancelResult)
  return RequestTask.pure { cancelled := ← state.cancelNamed req.runId }
