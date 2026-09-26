/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The List phase and the plan: the runner's `plan` subcommand asks every test executable for its
inventory, applies the filters, resolves what each selected test and each fixture it reaches
receives, and writes the plan, which names the needs that the selection reaches. The `list`
subcommand prints a plan, and the `check` subcommand reads the command line for the driver before
anything is built.
-/
module

public import Errata.RunnerConfig
public import Errata.Resolution
public import Errata.Dispatcher
public import Errata.ProcessControl
public import Errata.CommandLine
public import Std.Sync.Mutex

public section

set_option linter.missingDocs true
set_option doc.verso true

open Lean (Json ToJson FromJson)

namespace Errata.Runner

open ProcessControl

/-- Whether a character can appear unquoted in a word for a POSIX shell. -/
private def shellSafe (c : Char) : Bool :=
  c.isAlphanum || "_-./:=@%+,".contains c

/-- A word quoted for a POSIX shell: as it is when that is safe, and in single quotes otherwise. -/
def shellQuote (s : String) : String :=
  if !s.isEmpty && s.all shellSafe then s
  else "'" ++ s.replace "'" "'\\''" ++ "'"

/-- What a registry holds. -/
structure Registry.Contents where
  /-- Whether the run has been cancelled. -/
  cancelled : Bool := false
  /-- The process group of each running process. -/
  groups : Array Group := #[]
  /-- Whether the run has ended, including the teardowns that follow a cancellation. -/
  done : Bool := false
  /-- How long the teardowns that a cancelled run started may take, in milliseconds. -/
  allowanceMs : Nat := 0

/--
The processes of a run that are running, and whether the run has been cancelled. Every process
starts under the lock, after a check of the cancellation. Once the run is cancelled, every later
start is refused, except the teardowns of the fixtures whose setups were invoked.
-/
structure Registry where
  /-- The registry's contents. -/
  state : Std.Mutex Registry.Contents

/-- A registry with nothing running. -/
def Registry.new : BaseIO Registry := do
  return { state := ← Std.Mutex.new {} }

/--
Starts a process with {name}`start` and records it. If the run has been cancelled and
{name}`afterCancel` is false, the result is {lean}`none` and {name}`start` is skipped. Teardowns set
{name}`afterCancel`, and each start after a cancellation extends the time that the cancelled run may
take by {name}`allowanceMs`.
-/
def Registry.start (r : Registry) (start : IO Group) (afterCancel : Bool := false)
    (allowanceMs : Nat := 0) : IO (Option Group) :=
  r.state.atomically do
    let c ← get
    if c.cancelled && !afterCancel then return none
    let g ← start
    set { c with
      groups := c.groups.push g
      allowanceMs := c.allowanceMs + if c.cancelled then allowanceMs else 0 }
    return some g

/-- Forgets a process that the run has finished with. -/
def Registry.release (r : Registry) (g : Group) : IO Unit :=
  r.state.atomically (modify fun c => { c with groups := c.groups.filter (·.pid != g.pid) })

/-- Whether the run has been cancelled. -/
def Registry.cancelled (r : Registry) : IO Bool :=
  r.state.atomically (return (← get).cancelled)

/-- Records that the run has ended. -/
def Registry.finish (r : Registry) : IO Unit :=
  r.state.atomically (modify ({ · with done := true }))

/--
Cancels the run: every later start is refused, except teardowns, every running group is asked to
terminate, and those of them whose first process is still running after {name}`graceMs`
milliseconds are killed. The parts of the run that started the processes wait for them.
-/
def Registry.cancel (r : Registry) (graceMs : Nat) : IO Unit := do
  let groups ← r.state.atomically do
    let c ← get
    set { c with cancelled := true }
    return c.groups
  for g in groups do g.terminate
  let deadline := (← IO.monoMsNow) + graceMs
  repeat
    let live ← groups.filterM (·.armed.get)
    if live.isEmpty || (← IO.monoMsNow) ≥ deadline then break
    IO.sleep pollMs
  for g in groups do g.kill

/--
The environment variable that asks a process to treat its standard input as its lifeline, and to
end when it closes.
-/
def lifelineVariable : String := "ERRATA_LIFELINE"

/-- A new run identifier: 64 random bits, written as 16 hexadecimal digits. -/
def newRunId : IO String := do
  let bytes ← IO.getRandomBytes 8
  let hex (n : Nat) : String := String.singleton (Nat.digitChar n)
  return bytes.foldl (init := "") fun acc b => acc ++ hex (b.toNat / 16) ++ hex (b.toNat % 16)

/--
The environment variables that every test executable of the configuration receives.
{lit}`LEAN_ABORT_ON_PANIC` is {lit}`1`, so a panic ends the process that panicked, and
{lit}`ERRATA_RUN_ID` is {name}`runId`, the same for every process of one run.
-/
def executableEnv (config : Config) (runId : String) (exe : ExecutableConfig) :
    Array (String × Option String) :=
  #[("LEAN_ABORT_ON_PANIC", some "1"), (lifelineVariable, some "1"),
      ("ERRATA_RUN_ID", some runId)] ++
    (config.errataDir?.map fun d => #[("ERRATA_DIR", some d)]).getD #[] ++
    exe.env.map fun (k, v) => (k, some v)

/--
The pipe grace, in milliseconds: how long the processes that a test executable started may hold its
output pipes after it exits.
-/
def pipeGraceMs : Nat := 500

/--
Waits for the readers of a process's output pipes once the process has exited. When processes that
it started still hold the pipes after the pipe grace, {name}`Group.sweep` ends its group with the
pipe grace as the sweep's grace period, and the readers then get one more pipe grace.
-/
def releasePipes (g : Group) (readers : List (Task (Except IO.Error Unit))) : IO Unit := do
  unless ← waitAtMost pipeGraceMs readers do
    g.sweep pipeGraceMs
    discard <| waitAtMost pipeGraceMs readers

/-! # The List phase -/

/-- What the listing of the test executables needs. -/
structure ListContext where
  /-- The configuration, whose test executables are listed. -/
  config : Config
  /-- The processes that are running, and whether the run has been cancelled. -/
  registry : Registry
  /-- The identifier that the listings receive as {lit}`ERRATA_RUN_ID`. -/
  runId : String
  /-- A directory for the list files. -/
  dir : System.FilePath
  /-- How long a test executable may take to list its tests, in milliseconds. -/
  timeoutMs : Nat := defaultTimeoutMs
  /-- How long a listing that ran past its timeout has before it is killed, in milliseconds. -/
  gracePeriodMs : Nat := defaultGracePeriodMs

/--
Runs a command in a process group of its own, with the listing's timeout and grace period, and
returns its exit code with what it wrote to standard output and standard error. The exit code is
{lean}`none` when it timed out. The whole result is {lean}`none` when the run has been cancelled.
-/
def runListing (ctx : ListContext) (exe : ExecutableConfig) (args : Array String) :
    IO (Option (Option UInt32 × String × String)) := do
  let some cmd := exe.command[0]? | throw <| .userError "the command is empty"
  let some g ← ctx.registry.start
      (spawnGroup cmd (exe.command.extract 1 exe.command.size ++ args) exe.cwd?
        (executableEnv ctx.config ctx.runId exe))
    | return none
  let out ← IO.mkRef ""
  let err ← IO.mkRef ""
  let outTask ← IO.asTask (prio := .dedicated)
    (forwardLines g.child.stdout fun l => out.modify (· ++ l))
  let errTask ← IO.asTask (prio := .dedicated)
    (forwardLines g.child.stderr fun l => err.modify (· ++ l))
  let finished ← g.waitAtMost ctx.timeoutMs
  unless finished do discard <| g.terminateGraceKill ctx.gracePeriodMs
  let code ← g.wait
  releasePipes g [outTask, errTask]
  ctx.registry.release g
  return some (if finished then some code else none, ← out.get, ← err.get)

/-- The report of a test executable that could not list its tests. -/
private def listFailure (exe : ExecutableConfig) (why stdout stderr : String) : String :=
  let streams :=
    (if stdout.isEmpty then "" else s!"\nstdout:\n{stdout}") ++
    (if stderr.isEmpty then "" else s!"\nstderr:\n{stderr}")
  s!"the test executable {exe.name} could not list its tests: {why}\n\
    command: {" ".intercalate (exe.command.toList.map shellQuote)} errata-list <out>{streams}"

/--
Asks one test executable for its inventory. The result is its settings and its tests, or the message
that says why it could not list them.
-/
def listExecutable (ctx : ListContext) (idx : Nat) (exe : ExecutableConfig) :
    IO (Except String Listing) := do
  let file := ctx.dir / s!"list-{idx}.jsonl"
  IO.FS.writeFile file ""
  let listing ←
    try runListing ctx exe #["errata-list", file.toString]
    catch e => return .error (listFailure exe s!"it could not be started: {e}" "" "")
  let some (code?, stdout, stderr) := listing
    | return .error (listFailure exe "the run was cancelled" "" "")
  let fail (why : String) := Except.error (listFailure exe why stdout stderr)
  let some code := code?
    | return fail s!"it did not finish within {ctx.timeoutMs}ms"
  unless code == 0 do
    return match signalOfExitCode? code with
      | some s => fail s!"it was ended by signal {s} (exit code {code})"
      | none => fail s!"it exited with code {code}"
  let text ← IO.FS.readFile file
  let lines := text.splitOn "\n" |>.filter (!·.trimAscii.isEmpty)
  if lines.isEmpty then return fail "it wrote nothing to its list file"
  let mut sawProtocol := false
  let mut settings : Array SettingInfo := #[]
  let mut fixtures : Array InventoryFixture := #[]
  let mut tests : Array InventoryTest := #[]
  let mut names : Std.HashSet String := {}
  for line in lines do
    match Protocol.Record.parseLine line with
    | .error e => return fail s!"its list file has a line that could not be read: {e}"
    | .ok none => continue
    | .ok (some (_, record)) =>
      match record with
      | .protocol v? =>
        let v := v?.getD 0
        unless Protocol.minVersion ≤ v && v ≤ Protocol.maxVersion do
          return fail s!"it speaks protocol version {v}, and this runner accepts versions \
            {Protocol.minVersion} to {Protocol.maxVersion}"
        sawProtocol := true
      | .setting name? description? default? =>
        unless sawProtocol do return fail "its list file does not begin with a protocol record"
        let some name := name? | return fail "its list file has a setting without a name"
        if settings.any (·.name == name) then
          return fail s!"it declares the setting {name} more than once"
        settings := settings.push { name, description?, default? }
      | .fixture info =>
        unless sawProtocol do return fail "its list file does not begin with a protocol record"
        let some name := info.name? | return fail "its list file has a fixture without a name"
        if fixtures.any (·.name == name) then
          return fail s!"it declares the fixture {name} more than once"
        unless tests.isEmpty do
          return fail s!"it declares the fixture {name} after a test; fixtures precede tests"
        let deps := info.fixtures?.getD #[]
        if let some d := deps.find? (fun d => !fixtures.any (·.name == d)) then
          return fail s!"its fixture {name} takes the fixture {d}, which is not declared before it"
        fixtures := fixtures.push {
          name, description? := info.description?, settings := info.settings?.getD #[]
          fixtures := deps, threads? := info.threads?
        }
      | .test info =>
        unless sawProtocol do return fail "its list file does not begin with a protocol record"
        let some name := info.name? | return fail "its list file has a test without a name"
        -- The inventory leaves out benchmarks.
        if info.kind? == some "benchmark" then continue
        if names.contains name then return fail s!"it lists the test {name} more than once"
        names := names.insert name
        let uses := info.fixtures?.getD #[]
        if let some d := uses.find? (fun d => !fixtures.any (·.name == d.name)) then
          return fail s!"its test {name} uses the fixture {d.name}, which is not declared before it"
        if let some d := uses.find? (fun d => (uses.filter (·.name == d.name)).size > 1) then
          return fail s!"its test {name} uses the fixture {d.name} twice"
        tests := tests.push {
          exeIdx := idx, name, path := info.path?.getD #[], file? := info.file?,
          line? := info.line?, description? := info.description?, tags := info.tags?.getD #[]
          settings := info.settings?.getD #[], fixtures := uses, threads? := info.threads?
        }
      | _ => unless sawProtocol do
          return fail "its list file does not begin with a protocol record"
  unless sawProtocol do return fail "its list file has no protocol record"
  return .ok { settings, fixtures, tests }

/--
Asks every test executable for its inventory, in parallel. The result is each executable's listing,
or the messages of those that could not list, in the configuration's order.
-/
def listAll (ctx : ListContext) : IO (Except (Array String) (Array Listing)) := do
  let listings ← ctx.config.executables.mapIdxM fun i exe =>
    IO.asTask (prio := .dedicated) (listExecutable ctx i exe)
  let mut out := #[]
  let mut failures := #[]
  for task in listings do
    match ← IO.wait task with
    | .ok (.ok l) => out := out.push l
    | .ok (.error msg) => failures := failures.push msg
    | .error e => failures := failures.push s!"a test executable could not list: {e}"
  return if failures.isEmpty then .ok out else .error failures

/-- The message of a configuration that has no profile with the given name. -/
def unknownProfile (config : Config) (name : String) : String :=
  s!"the configuration has no profile named {name}; its profiles are \
    {", ".intercalate config.profileNames.toList}"

/--
The filters of a run, parsed: the selection, from the command line's filters and the profile's
default filter, or the configuration's when the profile has none, and each override's filter. If
some filters do not parse, or the default filter contains {lit}`default()`, then the result is
their messages with the exit code they end the run with: {name}`ExitCode.setupError` when a filter
of the configuration is among them, and {name}`ExitCode.invalidFilter` otherwise.
-/
def parseSelection (config : Config) (opts : Options) (profile : Profile) :
    Except (Array String × UInt32) (Selection × Array (SourcedFilter × Override)) := do
  let mut errors := #[]
  let mut configErrors := false
  let mut defaultFilter? : Option SourcedFilter := none
  if let some f := profile.defaultFilter? <|> config.defaultFilter? then
    match SourcedFilter.parse f.text f.source with
    | .ok sf =>
      match sf.expr.defaultSpan? with
      | some span =>
        errors := errors.push s!"{sf.at span.start}: default() stands for the default filter, so \
          the default filter cannot contain it"
        configErrors := true
      | none => defaultFilter? := some sf
    | .error e =>
      errors := errors.push e
      configErrors := true
  let mut filters := #[]
  for f in opts.filters do
    match SourcedFilter.parse f (.argument "--filter") with
    | .ok sf => filters := filters.push sf
    | .error e => errors := errors.push e
  let mut overrides := #[]
  for o in profile.overrides do
    match SourcedFilter.parse o.filter.text o.filter.source with
    | .ok sf => overrides := overrides.push (sf, o)
    | .error e =>
      errors := errors.push e
      configErrors := true
  unless errors.isEmpty do
    throw (errors, if configErrors then ExitCode.setupError else ExitCode.invalidFilter)
  let selection : Selection := {
    filters, names := opts.nameFilters, skips := opts.skips, exact := opts.exact
    default? := defaultFilter?, useDefault := !opts.ignoreDefaultFilter }
  return (selection, overrides)

/--
The fixtures of {name}`listing` that {name}`tests` use, directly or through the fixtures they take,
in the listing's order.
-/
def reachedFixtures (listing : Listing) (tests : Array InventoryTest) :
    Array InventoryFixture := Id.run do
  let mut reached : Std.HashSet String := {}
  for t in tests do
    for f in t.fixtures do reached := reached.insert f.name
  -- Each fixture is listed after the fixtures it takes, so one pass from the end reaches them all.
  for f in listing.fixtures.reverse do
    if reached.contains f.name then
      for d in f.fixtures do reached := reached.insert d
  return listing.fixtures.filter (reached.contains ·.name)

/-! # The plan -/

/-- The version of the plan's format. -/
def planVersion : Nat := 1

/-- A selected test in the plan, with what it receives. -/
structure PlannedTest where
  /-- The test, as its test executable lists it. -/
  test : InventoryTest
  /-- What it receives. -/
  resolution : PlannedResolution
deriving Repr, Inhabited

/-- A fixture that the selected tests reach, in the plan, with what its phases receive. -/
structure PlannedFixture where
  /-- The position of the fixture's executable in the configuration. -/
  exeIdx : Nat
  /-- The fixture, as its test executable lists it. -/
  fixture : InventoryFixture
  /-- What its phases receive. -/
  resolution : PlannedResolution
deriving Repr, Inhabited

/-- A need that the selected tests reach, with the tests that reach it. -/
structure PlannedNeed where
  /-- The need. -/
  need : Need
  /--
  The tests that reach it, each with its executable's name: the tests that take a setting that
  refers to it, and those that use a fixture that does, directly or through other fixtures.
  -/
  tests : Array (String × String)
deriving Repr, Inhabited

/--
The plan: what the List phase found and what the Run phase runs. It has the configuration, the
selected profile, the run's seed when the command line gives one, the declarations of each test
executable, the selected tests and the fixtures they reach with what each receives, the needs that
they reach, the issues that the List phase found, and the number of listed tests that the filters
left out.
-/
structure Plan where
  /-- The configuration, with the test executables that were listed. -/
  config : Config
  /-- The selected profile's name. -/
  profile : String := "default"
  /-- The run's seed, when the command line gives one. -/
  seed? : Option Nat := none
  /-- The run's seed: the command line's, or one that the {lit}`plan` subcommand drew. -/
  runSeed : Nat := 0
  /--
  Whether the {lit}`plan` subcommand began the events file: the {lit}`protocol` record and the List
  phase's {lit}`phase` record.
  -/
  eventsBegun : Bool := false
  /--
  The settings and the fixtures that each test executable declares, in the configuration's order.
  -/
  listings : Array Listing := #[]
  /-- The selected tests, in the inventory's order. -/
  tests : Array PlannedTest := #[]
  /--
  The fixtures that the selected tests reach, grouped by executable in the configuration's order,
  each after the fixtures it takes.
  -/
  fixtures : Array PlannedFixture := #[]
  /-- The needs that the selected tests reach, in the order of the {lit}`[needs]` table. -/
  needs : Array PlannedNeed := #[]
  /-- The issues that the List phase found, in the order it found them. -/
  issues : Array RunReport.Issue := #[]
  /-- The number of listed tests that the filters left out. -/
  skipped : Nat := 0
deriving Inhabited

/-- The name of the test executable at position {name}`i` of the plan's configuration. -/
def Plan.exeName (plan : Plan) (i : Nat) : String :=
  (plan.config.executables[i]?.map (·.name)).getD ""

instance : ToJson SettingInfo where
  toJson s := Json.mkObj <|
    [("name", Json.str s.name)] ++ Protocol.opt "description" s.description? ++
      Protocol.opt "default" s.default?

instance : FromJson SettingInfo where
  fromJson? j := do
    return { name := ← j.getObjValAs? String "name", description? := ← configField j "description"
             default? := ← configField j "default" }

instance : ToJson InventoryFixture where
  toJson f := Json.mkObj <|
    [("name", Json.str f.name)] ++ Protocol.opt "description" f.description? ++
    [("settings", ToJson.toJson f.settings), ("fixtures", ToJson.toJson f.fixtures)] ++
    Protocol.opt "threads" f.threads?

instance : FromJson InventoryFixture where
  fromJson? j := do
    return {
      name := ← j.getObjValAs? String "name", description? := ← configField j "description"
      settings := (← configField j "settings").getD #[]
      fixtures := (← configField j "fixtures").getD #[]
      threads? := ← configField j "threads" }

instance : ToJson InventoryTest where
  toJson t := Json.mkObj <|
    [("exe", ToJson.toJson t.exeIdx), ("name", Json.str t.name), ("path", ToJson.toJson t.path)] ++
    Protocol.opt "file" t.file? ++ Protocol.opt "line" t.line? ++
    Protocol.opt "description" t.description? ++
    [("tags", ToJson.toJson t.tags), ("settings", ToJson.toJson t.settings),
      ("fixtures", ToJson.toJson t.fixtures)] ++ Protocol.opt "threads" t.threads?

instance : FromJson InventoryTest where
  fromJson? j := do
    return {
      exeIdx := ← j.getObjValAs? Nat "exe", name := ← j.getObjValAs? String "name"
      path := (← configField j "path").getD #[], file? := ← configField j "file"
      line? := ← configField j "line"
      description? := ← configField j "description", tags := (← configField j "tags").getD #[]
      settings := (← configField j "settings").getD #[]
      fixtures := (← configField j "fixtures").getD #[]
      threads? := ← configField j "threads" }

instance : ToJson Listing where
  toJson l := Json.mkObj
    [("settings", ToJson.toJson l.settings), ("fixtures", ToJson.toJson l.fixtures)]

instance : FromJson Listing where
  fromJson? j := do
    return { settings := (← configField j "settings").getD #[]
             fixtures := (← configField j "fixtures").getD #[] }

instance : ToJson PlannedValue where
  toJson
    | .text v => Json.str v
    | .need n => Json.mkObj [("needs", Json.str n)]
    | .derivedSeed => Json.mkObj [("derived-seed", Json.bool true)]

instance : FromJson PlannedValue where
  fromJson? j :=
    match j.getStr? with
    | .ok s => .ok (.text s)
    | .error _ =>
      match j.getObjValAs? String "needs" with
      | .ok n => .ok (.need n)
      | .error _ =>
        if (j.getObjValAs? Bool "derived-seed").toOption == some true then .ok .derivedSeed
        else .error "a planned value is a string, a need, or the derived seed"

instance : ToJson PlannedResolution where
  toJson r := Json.mkObj [
    ("values", Json.arr (r.values.map fun (k, v) =>
      Json.mkObj [("name", Json.str k), ("value", ToJson.toJson v)])),
    ("missing", ToJson.toJson r.missing), ("timeout-ms", ToJson.toJson r.timeoutMs),
    ("grace-period-ms", ToJson.toJson r.gracePeriodMs),
    ("slow-after-ms", ToJson.toJson r.slowAfterMs), ("update-golden", Json.bool r.updateGolden)]

instance : FromJson PlannedResolution where
  fromJson? j := do
    let values : Array Json := (← configField j "values").getD #[]
    return {
      values := ← values.mapM fun v => do
        return (← v.getObjValAs? String "name", ← v.getObjValAs? PlannedValue "value")
      missing := (← configField j "missing").getD #[]
      timeoutMs := ← j.getObjValAs? Nat "timeout-ms"
      gracePeriodMs := ← j.getObjValAs? Nat "grace-period-ms"
      slowAfterMs := ← j.getObjValAs? Nat "slow-after-ms"
      updateGolden := (← configField j "update-golden").getD false }

/--
The plan as JSON. Each need has its name, its target with the target's position in the
configuration file, and the tests that reach it, so that the driver builds the need and names those
tests when the build fails.
-/
def Plan.toJson (plan : Plan) : Json :=
  Json.mkObj <| [
    ("protocol", ToJson.toJson planVersion), ("profile", Json.str plan.profile)] ++
    Protocol.opt "seed" plan.seed? ++ Protocol.opt "invocation" plan.config.invocation? ++ [
    ("run-seed", ToJson.toJson plan.runSeed), ("events-begun", Json.bool plan.eventsBegun),
    ("config", plan.config.toJson),
    ("listings", ToJson.toJson plan.listings),
    ("tests", Json.arr (plan.tests.map fun t =>
      Json.mkObj [("test", ToJson.toJson t.test), ("resolution", ToJson.toJson t.resolution)])),
    ("fixtures", Json.arr (plan.fixtures.map fun f =>
      Json.mkObj [("exe", ToJson.toJson f.exeIdx), ("fixture", ToJson.toJson f.fixture),
        ("resolution", ToJson.toJson f.resolution)])),
    ("needs", Json.arr (plan.needs.map fun n =>
      Json.mkObj [("name", Json.str n.need.name), ("target", Json.str n.need.target),
        ("line", ToJson.toJson n.need.line), ("col", ToJson.toJson n.need.col),
        ("tests", Json.arr (n.tests.map fun (e, t) =>
          Json.mkObj [("exe", Json.str e), ("test", Json.str t)]))])),
    ("issues", ToJson.toJson plan.issues),
    ("skipped", ToJson.toJson plan.skipped)]

/-- Decodes a plan. Errors name the key. -/
def Plan.fromJson? (j : Json) : Except String Plan := do
  let version ← j.getObjValAs? Nat "protocol" |>.mapError (s!"protocol: " ++ ·)
  unless version == planVersion do
    throw s!"the plan's version is {version}, and this runner reads version {planVersion}"
  let config ← Config.fromJson? (j.getObjValD "config") |>.mapError (s!"config: " ++ ·)
  let testOf (t : Json) : Except String PlannedTest := do
    return { test := ← t.getObjValAs? InventoryTest "test"
             resolution := ← t.getObjValAs? PlannedResolution "resolution" }
  let fixtureOf (f : Json) : Except String PlannedFixture := do
    return { exeIdx := ← f.getObjValAs? Nat "exe"
             fixture := ← f.getObjValAs? InventoryFixture "fixture"
             resolution := ← f.getObjValAs? PlannedResolution "resolution" }
  let reachingOf (t : Json) : Except String (String × String) := do
    return (← t.getObjValAs? String "exe", ← t.getObjValAs? String "test")
  let needOf (n : Json) : Except String PlannedNeed := do
    let tests : Array Json := (← configField n "tests").getD #[]
    let need : Need := {
      name := ← n.getObjValAs? String "name", target := ← n.getObjValAs? String "target"
      line := (← configField n "line").getD 0, col := (← configField n "col").getD 0 }
    return { need, tests := ← tests.mapM reachingOf }
  let tests : Array Json := (← configField j "tests").getD #[]
  let fixtures : Array Json := (← configField j "fixtures").getD #[]
  let needs : Array Json := (← configField j "needs").getD #[]
  return {
    config, profile := ← j.getObjValAs? String "profile", seed? := ← configField j "seed"
    runSeed := (← configField j "run-seed").getD 0
    eventsBegun := (← configField j "events-begun").getD false
    listings := ← (j.getObjValAs? (Array Listing) "listings" |>.mapError (s!"listings: " ++ ·))
    tests := ← tests.mapIdxM fun i t => testOf t |>.mapError (s!"tests[{i}]: " ++ ·)
    fixtures := ← fixtures.mapIdxM fun i f => fixtureOf f |>.mapError (s!"fixtures[{i}]: " ++ ·)
    needs := ← needs.mapIdxM fun i n => needOf n |>.mapError (s!"needs[{i}]: " ++ ·)
    issues := (← configField j "issues").getD #[]
    skipped := (← configField j "skipped").getD 0 }

/-- Reads a plan from a file, with the file's path in any error. -/
def Plan.load (path : System.FilePath) : IO Plan := do
  IO.ofExcept (Plan.fromJson? (← readJsonFile path) |>.mapError (s!"{path}: " ++ ·))

/--
The needs that the selected tests reach, in the order of the configuration's {lit}`[needs]` table,
each with the tests that reach it. A test reaches the needs that its own values refer to and those
that the values of the fixtures it uses refer to, directly or through other fixtures. The result is
an error that names a reference to a need that the configuration lacks.
-/
def reachedNeeds (config : Config) (tests : Array PlannedTest) (fixtures : Array PlannedFixture) :
    Except String (Array PlannedNeed) := do
  -- Each fixture comes after the fixtures it takes, so one pass in order gathers every need.
  let mut ofFixture : Std.HashMap (Nat × String) (Array String) := {}
  for f in fixtures do
    let inherited := f.fixture.fixtures.flatMap fun d => (ofFixture.get? (f.exeIdx, d)).getD #[]
    ofFixture := ofFixture.insert (f.exeIdx, f.fixture.name) (f.resolution.needs ++ inherited)
  let exeName (i : Nat) : String := (config.executables[i]?.map (·.name)).getD ""
  let mut reaching : Std.HashMap String (Array (String × String)) := {}
  for t in tests do
    let direct := t.resolution.needs
    let viaFixtures := t.test.fixtures.flatMap fun d =>
      (ofFixture.get? (t.test.exeIdx, d.name)).getD #[]
    for n in direct ++ viaFixtures do
      let key := (exeName t.test.exeIdx, t.test.name)
      let known := (reaching.get? n).getD #[]
      unless known.contains key do reaching := reaching.insert n (known.push key)
  for (n, ts) in reaching.toArray do
    unless config.needs.any (·.name == n) do
      let (e, t) := ts[0]!
      throw s!"the test {t} of {e} takes a setting that refers to the need {n}, and the \
        configuration's [needs] table has no entry of that name"
  return config.needs.filterMap fun need =>
    (reaching.get? need.name).map ({ need, tests := · })

/--
Makes the plan of a run: the List phase and what follows it before anything runs. Unknown profiles
and filters with syntax errors end the planning before the List phase. The List phase lists every
executable, then checks the configuration against the inventory: values that the command line gives
to settings that no executable declares are errors, and those that the profile gives are warnings;
the filters are evaluated, with a warning for each atom and each filter that selects nothing. The
configuration's filters draw these warnings only when the run has every test executable of the
package. Then the selected tests and the fixtures they reach are resolved, with each need as the
name that the settings refer to and each derived seed as such.

Each issue goes to {name}`report` as it is found, and {name}`onList` runs as the List phase begins.
The result is the plan, whose issues are those reported, or the exit code of the problem that ended
the planning.
-/
def makePlan (config : Config) (opts : Options) (registry : Registry) (runId : String)
    (report : RunReport.Issue → IO Unit := fun _ => pure ()) (onList : IO Unit := pure ()) :
    IO (Except UInt32 Plan) := do
  let issues ← IO.mkRef (#[] : Array RunReport.Issue)
  let raise (isError : Bool) (message : String) : IO Unit := do
    let issue : RunReport.Issue := { isError, message }
    issues.modify (·.push issue)
    report issue
  for w in config.warnings do raise false w
  let some profile := config.profile? opts.profile
    | raise true (unknownProfile config opts.profile)
      return .error ExitCode.setupError
  let (selection, overrides) ← match parseSelection config opts profile with
    | .ok fs => pure fs
    | .error (errors, code) =>
      for e in errors do raise true e
      return .error code
  IO.FS.withTempDir fun dir => do
    onList
    let ctx : ListContext := {
      config, registry, runId, dir
      timeoutMs := opts.timeoutMs? <|> profile.timeoutMs? |>.getD defaultTimeoutMs
      gracePeriodMs := opts.gracePeriodMs? <|> profile.gracePeriodMs? |>.getD defaultGracePeriodMs }
    let listings ← match ← listAll ctx with
      | .ok ls => pure ls
      | .error failures =>
        for f in failures do raise true f
        return .error ExitCode.listFailed
    let inventory := listings.flatMap (·.tests)
    let exeName (t : InventoryTest) : String := config.executables[t.exeIdx]!.name
    let resolution : ResolutionContext := {
      sets := opts.sets, profile, overrides, timeoutMs? := opts.timeoutMs?
      fixtureTimeoutMs? := opts.fixtureTimeoutMs?, gracePeriodMs? := opts.gracePeriodMs?
      updateGolden := opts.updateGolden, default? := selection.default? }
    -- A value for `Errata.updateGolden` given as a setting stops the run.
    let golden := resolution.updateGoldenValues
    for m in golden do raise true m
    unless golden.isEmpty do return .error ExitCode.setupError
    -- Values that the command line gives to settings that nothing declares stop the run. Those that
    -- the configuration gives are warnings, since profiles serve the executables of every library
    -- and runs may select some of them. A run that selects only some of them reports none of these.
    let declared := listings.flatMap (·.settings.map (·.name))
    let undeclared := resolution.undeclared declared |>.filter fun u =>
      u.commandLine || !config.partialSelection
    let names := declared.foldl (init := #[]) fun acc n =>
      if acc.contains n then acc else acc.push n
    for u in undeclared do
      raise u.commandLine s!"{u.place} gives the setting {u.name} a value, and no test executable \
        of this run declares it; the declared settings are \
        {if names.isEmpty then "none" else ", ".intercalate names.toList}"
    if undeclared.any (·.commandLine) then return .error ExitCode.setupError
    let records := inventory.map fun t => t.record (exeName t)
    -- An `exe(…)` is judged against every executable of the package, those that the filters ruled
    -- out before building included.
    let exes := config.executableNames
    -- The configuration's filters serve every executable of the package, so they are checked
    -- against the inventory only when the run has all of them. The command line's always are.
    let checked := selection.filters ++
      (if config.partialSelection then #[] else selection.default?.toArray ++ overrides.map (·.1))
    for f in checked do
      for w in f.warnings records exes selection.defaultSelects do raise false w
    let tests : Array PlannedTest := inventory.filterMap fun t =>
      if selection.selects (t.record (exeName t)) then
        some { test := t
               resolution := resolution.planTest (exeName t) listings[t.exeIdx]!.settings t }
      else none
    let mut fixtures : Array PlannedFixture := #[]
    for h : e in [0 : listings.size] do
      let listing := listings[e]
      let own := tests.filterMap fun t => if t.test.exeIdx == e then some t.test else none
      for f in reachedFixtures listing own do
        fixtures := fixtures.push
          { exeIdx := e, fixture := f, resolution := resolution.planFixture listing.settings f }
    let needs ← match reachedNeeds config tests fixtures with
      | .ok ns => pure ns
      | .error e =>
        raise true e
        return .error ExitCode.setupError
    return .ok {
      config, profile := profile.name, seed? := opts.seed
      listings := listings.map ({ · with tests := #[] }), tests, fixtures, needs
      issues := ← issues.get, skipped := inventory.size - tests.size }

/-! # Printing a plan -/

/-- A value as a listing shows it, quoted so that an empty value shows. -/
private def showValue (v : String) : String := v.quote

/-- Text indented line by line. -/
private def indented (indent text : String) : String :=
  "\n".intercalate ((text.trimAscii.copy.splitOn "\n").map (indent ++ ·))

/--
The values that a test or a fixture's phases receive, in the order it takes the settings, with
{lit}`Errata.updateGolden` given the value {lit}`true` when golden checks rewrite their expected
files: where the settings list it, or at the end.
-/
def PlannedResolution.arguments (r : PlannedResolution) : Array (String × PlannedValue) :=
  if !r.updateGolden then r.values
  else if r.values.any (·.1 == updateGoldenSetting) then
    r.values.map fun (k, v) => if k == updateGoldenSetting then (k, .text "true") else (k, v)
  else r.values.push (updateGoldenSetting, .text "true")

/-- The selected tests, gathered by test executable in inventory order. -/
private def byExecutable (tests : Array PlannedTest) : Array (Nat × Array PlannedTest) :=
  tests.foldl (init := #[]) fun acc t =>
    match acc.back? with
    | some (i, group) =>
      if i == t.test.exeIdx then acc.pop.push (i, group.push t) else acc.push (t.test.exeIdx, #[t])
    | none => #[(t.test.exeIdx, #[t])]

/--
Prints the plan's tests in nextest's human format: each test executable's name and a colon, then
its selected tests, indented by four spaces. With {name}`verbose`, the settings that the test
executables declare come first when there are any, with their descriptions and defaults, and then
the fixtures they declare when there are any, with their descriptions, the threads they ask for, and
the settings and the fixtures they take; each test is followed by its file and line, its tags, its
description, the values it receives, and the fixtures it uses; and the mandatory settings that
nothing gives a value come last, with the tests that need them. A value that a need gives is shown
as the need's name. A seed derived from the run's seed is shown as its value under
{name}`seed?`, the seed that the command line gives, and as derived without one.
-/
def printHumanList (plan : Plan) (line : String → IO Unit) (color verbose : Bool)
    (seed? : Option Nat) : IO Unit := do
  let listings := plan.listings
  -- The settings' heading is printed only when a test executable declares a setting.
  if verbose && listings.any (!·.settings.isEmpty) then
    line "Settings:"
    let mut shown : Std.HashSet String := {}
    for l in listings do
      for s in l.settings do
        if shown.contains s.name then continue
        shown := shown.insert s.name
        let dflt := match s.default? with | some d => s!" (default {showValue d})" | none => ""
        line s!"  {s.name}{dflt}"
        if let some d := s.description? then line (indented "      " d)
  -- Likewise the fixtures' heading, only when a test executable declares a fixture.
  if verbose && listings.any (!·.fixtures.isEmpty) then
    line "Fixtures:"
    for l in listings do
      for f in l.fixtures do
        let threads := match f.threads? with | some n => s!" (threads {n})" | none => ""
        line s!"  {f.name}{threads}"
        if let some d := f.description? then line (indented "      " d)
        unless f.settings.isEmpty do line s!"      settings: {", ".intercalate f.settings.toList}"
        unless f.fixtures.isEmpty do line s!"      fixtures: {", ".intercalate f.fixtures.toList}"
  let mut missing : Array (String × String) := #[]
  for (idx, tests) in byExecutable plan.tests do
    line s!"{Style.exe.paint color (plan.exeName idx)}:"
    for pt in tests do
      let t := pt.test
      let r := pt.resolution
      let name := styleTestName color t.name t.path
      unless verbose do
        line s!"    {name}"
        continue
      let loc := match t.file?, t.line? with
        | some f, some l => s!"  ({f}:{l})"
        | some f, none => s!"  ({f})"
        | _, _ => ""
      let tags := if t.tags.isEmpty then "" else s!"  [{", ".intercalate t.tags.toList}]"
      line s!"    {name}{loc}{tags}"
      if let some d := t.description? then line (indented "        " d)
      -- The settings are those that the run sends.
      for (k, v) in r.arguments do
        match v, seed? with
        | .text s, _ => line s!"        {k} = {showValue s}"
        | .need n, _ => line s!"        {k}: the need {n}, built before the run"
        | .derivedSeed, some s =>
          line s!"        {k} = {showValue (toString (testSeed s (plan.exeName idx) t.name))}"
        -- Seeds derived from a random run seed differ in every run, so their values say nothing.
        | .derivedSeed, none => line s!"        {k}: derived from the run's seed"
      for f in t.fixtures do
        line s!"        uses {f.name}{if f.exclusive then "" else " (shared)"}"
      for m in r.missing do
        line s!"        {m}: no value"
        missing := missing.push (m, t.name)
  unless missing.isEmpty do
    line "Mandatory settings without a value:"
    for (m, t) in missing do
      line s!"  {m}, which {t} needs"

/--
Prints one line per selected test, in inventory order: the executable, the name, the file and line,
and the tags, in columns padded to their widest entry with two spaces between them.
-/
def printOnelineList (plan : Plan) (line : String → IO Unit) : IO Unit := do
  let rows := plan.tests.map fun pt =>
    let t := pt.test
    let loc := match t.file?, t.line? with
      | some f, some l => s!"{f}:{l}"
      | some f, none => f
      | _, _ => "-"
    let tags := if t.tags.isEmpty then "" else s!"[{", ".intercalate t.tags.toList}]"
    #[plan.exeName t.exeIdx, t.name, loc, tags]
  let width (i : Nat) : Nat := rows.foldl (fun w r => max w (r[i]!.length)) 0
  let widths := #[width 0, width 1, width 2]
  for r in rows do
    let cols := (List.range 3).map fun i => r[i]!.pushn ' ' (widths[i]! - r[i]!.length)
    line ("  ".intercalate (cols ++ [r[3]!]) |>.trimAsciiEnd.copy)

/--
The plan's selected tests as JSON: the profile, the run's seed {name}`runSeed`, the number of listed
tests selected and left out, under {lit}`not-built` the names of the libraries and executables that
the filters ruled out before building, the settings that the test executables declare, the needs
that the selected tests reach, and each test executable with its selected tests and the fixtures
they reach.
Each test has its name, path, file, line, tags, and description, the values it receives, the
mandatory settings without a value, whether its seed is derived from the run's, its timeout, grace
period, and slow mark in milliseconds, and the fixtures it uses, each exclusive or shared. A value
that a need gives is an object that names the need.
Each fixture has its name, description, the settings and the fixtures it takes, and the threads it
asks for.
-/
def inventoryJson (plan : Plan) (runSeed : Nat) : Json := Id.run do
  let opt {α} [ToJson α] (key : String) (v? : Option α) : List (String × Json) :=
    (v?.map fun v => (key, ToJson.toJson v)).toList
  let mut settings : Array Json := #[]
  let mut seen : Std.HashSet String := {}
  for l in plan.listings do
    for s in l.settings do
      if seen.contains s.name then continue
      seen := seen.insert s.name
      settings := settings.push <| Json.mkObj <| [("name", Json.str s.name)] ++
        opt "description" s.description? ++ opt "default" s.default?
  let valueJson (exe name : String) : PlannedValue → Json
    | .text v => Json.str v
    | .need n => Json.mkObj [("needs", Json.str n)]
    | .derivedSeed => Json.str (toString (testSeed runSeed exe name))
  let testJson (exe : String) (pt : PlannedTest) : Json :=
    let t := pt.test
    let r := pt.resolution
    Json.mkObj <|
      [("name", Json.str t.name), ("path", ToJson.toJson t.path)] ++ opt "file" t.file? ++
      opt "line" t.line? ++ [("tags", ToJson.toJson t.tags)] ++ opt "description" t.description? ++
      [("settings", Json.mkObj (r.arguments.toList.map fun (k, v) => (k, valueJson exe t.name v))),
        ("missing", ToJson.toJson r.missing), ("derived-seed", Json.bool r.derivedSeed),
        ("timeout-ms", ToJson.toJson r.timeoutMs),
        ("grace-period-ms", ToJson.toJson r.gracePeriodMs),
        ("slow-after-ms", ToJson.toJson r.slowAfterMs),
        ("fixtures", Json.arr (t.fixtures.map fun f =>
          Json.mkObj [("name", Json.str f.name), ("exclusive", Json.bool f.exclusive)]))]
  let groups := byExecutable plan.tests
  let executables := plan.config.executables.mapIdx fun i e =>
    let tests := (groups.find? (·.1 == i)).map (·.2) |>.getD #[]
    let fixtures := plan.fixtures.filterMap fun f => if f.exeIdx == i then some f.fixture else none
    Json.mkObj [("name", Json.str e.name), ("command", ToJson.toJson e.command),
      ("tests", Json.arr (tests.map (testJson e.name))),
      ("fixtures", Json.arr (fixtures.map ToJson.toJson))]
  return Json.mkObj [("profile", Json.str plan.profile), ("seed", ToJson.toJson runSeed),
    ("selected", ToJson.toJson plan.tests.size), ("skipped", ToJson.toJson plan.skipped),
    ("not-built", ToJson.toJson plan.config.ruledOut),
    ("settings", Json.arr settings),
    ("needs", Json.arr (plan.needs.map fun n =>
      Json.mkObj [("name", Json.str n.need.name), ("target", Json.str n.need.target)])),
    ("executables", Json.arr executables)]

/--
Prints the plan's selected tests in the format that {name}`opts` names, with {name}`line`. The run's
seed, {name}`runSeed`, gives derived seeds their values when the command line gives the seed, and
the JSON formats their values always.
-/
def printPlan (plan : Plan) (opts : Options) (line : String → IO Unit) (color : Bool)
    (runSeed : Nat) : IO Unit :=
  match opts.messageFormat with
  | .human =>
    printHumanList plan line color (opts.verbosity != .silent) (opts.seed.map fun _ => runSeed)
  | .oneline => printOnelineList plan line
  | .json => line (inventoryJson plan runSeed).compress
  | .jsonPretty => line (inventoryJson plan runSeed).pretty

/-! # The subcommands -/

/--
Reports a command line that could not be read, with the way to the usage text, and returns
{name}`ExitCode.usage`. If the command line asks for the usage text anywhere, then it prints that
text and returns {name}`ExitCode.ok`.
-/
def badCommandLine (args : List String) (invocation message : String) : IO UInt32 := do
  if args.any (fun a => a == "--help" || a == "-h") then
    IO.print (usage invocation)
    return ExitCode.ok
  IO.eprintln s!"error: {message}"
  IO.eprintln s!"Run `{invocation} --help` for the options."
  return ExitCode.usage

/--
Whether the human-readable output is colored, from the choice, the environment variable lookup
{name}`env`, and whether standard output is a terminal. For {lit}`auto`, a
{lit}`CLICOLOR_FORCE` that is set and is not {lit}`0` forces color, and otherwise a
{lit}`NO_COLOR` that is set and not empty disables it; without either, the output is colored when
it goes to a terminal.
-/
def colorOf (choice : ColorChoice) (env : String → Option String) (terminal : Bool) : Bool :=
  match choice with
  | .always => true
  | .never => false
  | .auto =>
    if (env "CLICOLOR_FORCE").any (fun v => !v.isEmpty && v != "0") then true
    else if (env "NO_COLOR").any (!·.isEmpty) then false
    else terminal

/-- Whether this process colors its human-readable output, as {name}`colorOf` decides. -/
def useColor (choice : ColorChoice) : IO Bool := do
  let force ← IO.getEnv "CLICOLOR_FORCE"
  let noColor ← IO.getEnv "NO_COLOR"
  let env (name : String) : Option String :=
    if name == "CLICOLOR_FORCE" then force else if name == "NO_COLOR" then noColor else none
  return colorOf choice env (← (← IO.getStdout).isTty)

/--
The {lit}`check` subcommand, {lit}`errata-runner check REQUEST OUT ARGS...`, which the driver runs
before it builds any test executable. {name}`request` is a JSON object with the path of
{lit}`config.json` under {lit}`config`, the command that the arguments follow under
{lit}`invocation`, and the names of the test executables that the package can have under
{lit}`executables`. The subcommand reads the command line {name}`args` as a run would, checks the
profile and the filters, and writes to the file {name}`out` a JSON object with the command, the
profile, the executables that the filters can select by their names alone, whether the phases are
named as they begin, and the modules that {lit}`--interpreted` names. When the command line asks for
the usage
text, the subcommand prints it and writes {lit}`{"help": true}`. The result is the exit code:
{name}`ExitCode.ok`, or the code of the problem, which the subcommand reports.
-/
def checkMain (request out : String) (args : List String) : IO UInt32 := do
  let req ← IO.ofExcept (Json.parse request)
  let invocation := (req.getObjValAs? String "invocation").toOption.getD "errata-runner"
  let configPath ← IO.ofExcept (req.getObjValAs? String "config")
  let candidates := (req.getObjValAs? (Array String) "executables").toOption.getD #[]
  let write (j : Json) : IO Unit := IO.FS.writeFile out (j.compress ++ "\n")
  let opts ← match parseCommandLine args (← IO.getEnv "ERRATA_PROFILE") with
    | .ok opts => pure opts
    | .error msg =>
      let code ← badCommandLine args invocation msg
      if code == ExitCode.ok then write (Json.mkObj [("help", Json.bool true)])
      return code
  if opts.help then
    IO.print (usage invocation)
    write (Json.mkObj [("help", Json.bool true)])
    return ExitCode.ok
  let config ←
    try IO.ofExcept (Config.ofJson (← readJsonFile configPath) (Json.mkObj []))
    catch e =>
      IO.eprintln s!"error: {e}"
      return ExitCode.setupError
  let some profile := config.profile? opts.profile
    | IO.eprintln s!"error: {unknownProfile config opts.profile}"
      return ExitCode.setupError
  match parseSelection config opts profile with
  | .error (errors, code) =>
    for e in errors do IO.eprintln s!"error: {e}"
    return code
  | .ok (selection, _) =>
    write <| Json.mkObj [("command", Json.str opts.command.name),
      ("profile", Json.str profile.name),
      ("executables", ToJson.toJson (candidates.filter selection.mayContain)),
      ("phases", Json.bool (opts.command == .run && opts.verbosity.showsPasses)),
      ("interpreted", ToJson.toJson opts.interpreted)]
    return ExitCode.ok

/-- The events file's first record: its version, the run's identifier, and the run's seed. -/
def protocolRecord (runId : String) (runSeed : Nat) : Json :=
  Json.mkObj [("type", Json.str "protocol"), ("version", ToJson.toJson Protocol.version),
    ("run_id", Json.str runId), ("seed", ToJson.toJson runSeed)]

/--
The run's identifier: {lit}`ERRATA_RUN_ID` when the driver gives it, so that the {lit}`plan` and
{lit}`run` subcommands of one run share it, and otherwise a new one.
-/
def runIdOfEnvironment : IO String := do
  match ← IO.getEnv "ERRATA_RUN_ID" with
  | some id => if id.isEmpty then newRunId else pure id
  | none => newRunId

/--
Ends the planning once the process's lifeline, its standard input, closes: the listings that run are
terminated and, after {name}`graceMs` milliseconds, killed, and the process exits with {lit}`1`.
-/
def cancelWhenStdinCloses (parentIn : IO.FS.Stream) (registry : Registry) (graceMs : Nat) :
    IO Unit := do
  repeat
    if (← parentIn.getLine).isEmpty then break
  try IO.eprintln "errata-runner: standard input closed, so the plan ends" catch _ => pure ()
  registry.cancel graceMs
  IO.Process.forceExit 1

/--
The {lit}`plan` subcommand, {lit}`errata-runner plan CONFIG EXECUTABLES OUT ARGS...`: it reads the
configuration from {lit}`config.json` at {name}`configPath` and {lit}`executables.json` at
{name}`executablesPath`, reads the command line {name}`args`, makes the plan, and writes it to the
file {name}`out`. The run's identifier is {name}`runIdOfEnvironment`'s, and the run's seed is the
command line's or one drawn here. As the List phase begins, it prints {lit}`== List` under
{lit}`-v`, and it begins the events file that {lit}`--events` names with the {lit}`protocol` record
and the List phase's {lit}`phase` record. When an issue ends the planning, no plan is written, the
issues found are printed on standard error, and the result is the exit code of the issue:
{name}`ExitCode.invalidFilter`, {name}`ExitCode.setupError`, or {name}`ExitCode.listFailed`.
Otherwise the plan holds the issues, which the run reports. When {lit}`ERRATA_LIFELINE` is
{lit}`1`, the subcommand watches its standard input and ends its listings when it closes. Once it
has begun, the subcommand flushes its output and ends the process itself.
-/
def planMain (configPath executablesPath out : String) (args : List String) : IO UInt32 := do
  let config ←
    try Config.load configPath executablesPath
    catch e =>
      IO.eprintln s!"error: {e}"
      return ExitCode.setupError
  let invocation := config.invocation?.getD "errata-runner plan CONFIG EXECUTABLES OUT"
  let opts ← match parseCommandLine args (← IO.getEnv "ERRATA_PROFILE") with
    | .ok opts => pure opts
    | .error msg => return ← badCommandLine args invocation msg
  if opts.help then
    IO.print (usage invocation)
    return ExitCode.ok
  let registry ← Registry.new
  if (← IO.getEnv lifelineVariable) == some "1" then
    let _ ← IO.asTask (prio := .dedicated) (cancelWhenStdinCloses (← IO.getStdin) registry
      (opts.gracePeriodMs?.getD defaultGracePeriodMs))
  let runId ← runIdOfEnvironment
  let runSeed ← match opts.seed with
    | some s => pure s
    | none => IO.rand 0 (2 ^ 32 - 1)
  let events? ← opts.eventsPath.mapM fun p => do
    if let some parent := (p : System.FilePath).parent then IO.FS.createDirAll parent
    IO.FS.Handle.mk p .append
  let stdout ← IO.getStdout
  let onList : IO Unit := do
    if let some h := events? then
      h.putStr ((protocolRecord runId runSeed).compress ++ "\n")
      h.putStr ((Json.mkObj [("type", Json.str "phase"), ("name", Json.str "List"),
        ("time_ms", ToJson.toJson (← Protocol.nowMs))]).compress ++ "\n")
      h.flush
    if opts.command == .run && opts.verbosity.showsPasses then
      stdout.putStrLn (phaseLine "List" none)
      stdout.flush
  let issues ← IO.mkRef (#[] : Array RunReport.Issue)
  let report (issue : RunReport.Issue) : IO Unit := issues.modify (·.push issue)
  let code ← match ← makePlan config opts registry runId report onList with
    | .error code =>
      for issue in ← issues.get do IO.eprintln s!"{issue.level}: {issue.message}"
      pure code
    | .ok plan =>
      if let some parent := (out : System.FilePath).parent then IO.FS.createDirAll parent
      let plan := { plan with runSeed, eventsBegun := events?.isSome }
      IO.FS.writeFile out (plan.toJson.compress ++ "\n")
      pure ExitCode.ok
  try stdout.flush catch _ => pure ()
  try (← IO.getStderr).flush catch _ => pure ()
  -- The thread that watches standard input runs until the pipe closes, and a Lean program that
  -- returns from `main` waits for its threads, so the subcommand ends the process itself.
  IO.Process.forceExit code.toUInt8

/--
The {lit}`list` subcommand, {lit}`errata-runner list PLAN ARGS...`: it prints the selected tests of
the plan at {name}`planPath` in the format that the command line {name}`args` names, and then the
plan's issues on standard error.
-/
def listMain (planPath : String) (args : List String) : IO UInt32 := do
  let plan ←
    try Plan.load planPath
    catch e =>
      IO.eprintln s!"error: {e}"
      return ExitCode.setupError
  let invocation := plan.config.invocation?.getD "errata-runner list PLAN"
  let opts ← match parseCommandLine args (← IO.getEnv "ERRATA_PROFILE") with
    | .ok opts => pure opts
    | .error msg => return ← badCommandLine args invocation msg
  if opts.help then
    IO.print (usage invocation)
    return ExitCode.ok
  let runSeed := plan.runSeed
  let stdout ← IO.getStdout
  printPlan plan { opts with seed := plan.seed? } (fun l => do stdout.putStrLn l; stdout.flush)
    (← useColor opts.color) runSeed
  for issue in plan.issues do
    IO.eprintln s!"{issue.level}: {issue.message}"
  return ExitCode.ok

end Errata.Runner
