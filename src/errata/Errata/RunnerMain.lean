/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The runner: it lists the tests of every test executable in its configuration, selects the tests that
the filters name, resolves what each receives, runs each in a process of its own under a timeout,
merges what the test executable reported with what it observed from outside, and writes the reports.
-/
module

public import Errata.RunnerConfig
public import Errata.Resolution
public import Errata.Dispatcher
public import Errata.ProcessControl
public import Cli
public import Std.Sync.Mutex
import all Errata.FS

public section

set_option linter.missingDocs true
set_option doc.verso true

open Lean (Json ToJson)

namespace Errata.Runner

open ProcessControl

/-- The runner's settings, from its command line. -/
structure Options where
  /-- The path of the configuration file. -/
  configPath : String := ""
  /-- The reporting verbosity. -/
  verbosity : Verbosity := .silent
  /-- Passes {lit}`setting:updateGolden=true` to every test. -/
  updateGolden : Bool := false
  /-- The run's seed, from which each test's seed is derived. -/
  seed : Option Nat := none
  /-- Writes a JUnit XML report to this path. -/
  junitPath : Option String := none
  /-- Writes a JSON report to this path. -/
  jsonPath : Option String := none
  /-- Writes a Markdown report to this path. -/
  markdownPath : Option String := none
  /-- Writes the run's events to this path as JSON lines. -/
  eventsPath : Option String := none
  /-- Fails the run if warnings are logged. -/
  wfail : Bool := false
  /-- How many tests may run at once. -/
  jobs : Nat := 1
  /-- Lists the settings and the tests that would run, without running them. -/
  list : Bool := false
  /-- How long a test may run before it is terminated, in milliseconds, over the configuration's. -/
  timeoutMs? : Option Nat := none
  /-- How long a terminated test has before it is killed, in milliseconds, over the configuration's. -/
  gracePeriodMs? : Option Nat := none
  /-- Values of settings, in order, from {lit}`--set NAME=VALUE`. -/
  sets : Array (String × String) := #[]
  /-- The profile of the configuration to run with. -/
  profile : String := "default"
  /-- The filters from {lit}`--filter`, joined by union. -/
  filters : Array String := #[]
  /--
  The filters of the {lit}`list` subcommand, when the runner was invoked with it: the runner lists
  the tests that they select and runs nothing.
  -/
  listFilters? : Option (Array String) := none
deriving Repr, Inhabited

/--
Parses a duration: a natural number followed by {lit}`ms`, {lit}`s`, {lit}`m`, or {lit}`h`. The
result is in milliseconds.
-/
def parseDuration (s : String) : Except String Nat :=
  let s := s.trimAscii.copy
  let num (digits : String) (scale : Nat) : Except String Nat :=
    match digits.toNat? with
    | some n => .ok (n * scale)
    | none => .error s!"invalid duration '{s}': expected a number followed by ms, s, m, or h"
  if let some d := s.dropSuffix? "ms" then num d.copy 1
  else if let some d := s.dropSuffix? "s" then num d.copy 1000
  else if let some d := s.dropSuffix? "m" then num d.copy 60000
  else if let some d := s.dropSuffix? "h" then num d.copy 3600000
  else .error s!"invalid duration '{s}': expected a number followed by ms, s, m, or h"

open Cli in
/--
The runner's command-line interface. The handler receives the parsed arguments. {name}`command` is
the command that the runner's options follow, shown in the usage header.
-/
def runnerCmd (command : String) (handler : Cli.Parsed → IO UInt32) : Cli.Cmd :=
  match cmd with
  | .init «meta» run subCmds extension? =>
    .init { «meta» with name := command } run subCmds extension?
where cmd := `[Cli|
    "errata-runner" VIA handler;
    "Runs the tests of the test executables that the configuration names."

    FLAGS:
      v, verbose;              "Also report passes, truncating each test's results."
      vv, "verbose-all";       "Report every result, without truncation."
      vvv, "verbose-docs";     "Report every result and every test's docstring."
      "update-golden";         "Rewrite the expected files of golden checks."
      seed : Nat;              "The run's seed, from which each test's seed is derived."
      junit : String;          "Write a JUnit XML report to the given path."
      json : String;           "Write a JSON report to the given path."
      markdown : String;       "Write a Markdown report (for a CI job summary) to the given path."
      events : String;         "Write the run's events to the given path as JSON lines."
      wfail;                   "Fail the run if warnings are logged."
      jobs : Nat;              "How many tests may run at once (1)."
      list;                    "List the settings and the tests that would run, and run nothing."
      timeout : String;        "How long a test may run before it is stopped, such as 90s or 10m (10m)."
      "grace-period" : String; "How long a stopped test has before it is killed (10s)."
      set : String;            "Give a setting a value, as NAME=VALUE. Repeatable."
      profile : String;        "The profile of the configuration file to run with (default)."
      filter : String;         "Run only the tests the filter selects. Repeatable; the filters are joined by union."

    ARGS:
      config : String;         "The configuration file that the driver writes."
      ...argument : String;    "The `list` subcommand and its filters; see below."

    EXTENSIONS:
      longDescription "With `list FILTER...` after the configuration file, the runner lists the \
        tests that the filters select, one per line, and runs nothing. No filter selects every \
        test, and the profile's default filter plays no part."
  ]

/-- The value of a path-valued flag, when it is present; a present but empty path is an error. -/
private def pathFlag (p : Cli.Parsed) (name : String) : Except String (Option String) :=
  match p.flag? name with
  | none => .ok none
  | some f => if f.value.isEmpty then .error s!"--{name} expects a path" else .ok (some f.value)

/--
Takes the repeatable options {lit}`--set` and {lit}`--filter` out of the arguments, in either the
{lit}`--name value` or the {lit}`--name=value` form, and returns their values with the other
arguments. Arguments after a {lit}`--` stay where they are.
-/
partial def takeRepeatable (args : List String) :
    Except String (Array String × Array String × List String) :=
  go #[] #[] #[] args
where
  go (sets filters : Array String) (rest : Array String) :
      List String → Except String (Array String × Array String × List String)
    | [] => .ok (sets, filters, rest.toList)
    | "--" :: after => .ok (sets, filters, (rest.push "--").toList ++ after)
    | "--set" :: v :: more => go (sets.push v) filters rest more
    | ["--set"] => .error "--set expects NAME=VALUE"
    | "--filter" :: v :: more => go sets (filters.push v) rest more
    | ["--filter"] => .error "--filter expects a filter"
    | arg :: more =>
      if let some v := arg.dropPrefix? "--set=" then go (sets.push v.copy) filters rest more
      else if let some v := arg.dropPrefix? "--filter=" then go sets (filters.push v.copy) rest more
      else go sets filters (rest.push arg) more

/-- Splits a {lit}`--set` value at its first {lit}`=`. The value is everything after it, taken verbatim. -/
def parseSet (s : String) : Except String (String × String) :=
  match s.splitOn "=" with
  | name :: value@(_ :: _) =>
    if name.isEmpty then .error s!"--set {s}: the setting's name is empty"
    else .ok (name, "=".intercalate value)
  | _ => .error s!"--set {s}: expected NAME=VALUE"

/--
Interprets a parsed command line as runner settings, with the values of the repeatable options that
{name}`takeRepeatable` took out.
-/
def optionsOfParsed (p : Cli.Parsed) (sets filters : Array String := #[]) : Except String Options := do
  let verbosity : Verbosity :=
    if p.hasFlag "verbose-docs" then .superVerbose
    else if p.hasFlag "verbose-all" then .verbose
    else if p.hasFlag "verbose" then .quiet
    else .silent
  let jobs := (p.flag? "jobs" |>.map (·.as! Nat)).getD 1
  if jobs == 0 then throw "--jobs 0 is invalid: at least one test must be able to run"
  unless jobs == 1 do
    throw s!"--jobs {jobs}: only --jobs 1 is supported"
  let timeoutMs? ← p.flag? "timeout" |>.mapM (parseDuration ·.value)
  if timeoutMs? == some 0 then throw "--timeout must be longer than zero"
  let gracePeriodMs? ← p.flag? "grace-period" |>.mapM (parseDuration ·.value)
  let listFilters? ← match (p.variableArgsAs! String).toList with
    | [] => pure none
    | "list" :: listed =>
      -- The subcommand applies exactly its filters, so an option would be silently ignored.
      let given := (p.flags.map (s!"--{·.flag.longName}")) ++
        (if sets.isEmpty then #[] else #["--set"]) ++ (if filters.isEmpty then #[] else #["--filter"])
      if let some opt := given[0]? then
        throw s!"the `list` subcommand takes filters only, and {opt} is an option of a run"
      pure (some listed.toArray)
    | arg :: _ =>
      throw s!"unexpected argument '{arg}': the runner's one subcommand is `list`, and a test's \
        settings are given with --set NAME=VALUE"
  return {
    configPath := (p.positionalArg? "config").map (·.value) |>.getD "",
    verbosity,
    updateGolden := p.hasFlag "update-golden",
    seed := p.flag? "seed" |>.map (·.as! Nat),
    junitPath := ← pathFlag p "junit",
    jsonPath := ← pathFlag p "json",
    markdownPath := ← pathFlag p "markdown",
    eventsPath := ← pathFlag p "events",
    wfail := p.hasFlag "wfail",
    jobs, list := p.hasFlag "list", timeoutMs?, gracePeriodMs?
    sets := ← sets.mapM parseSet
    profile := (p.flag? "profile" |>.map (·.value)).getD "default"
    filters, listFilters?
  }

/--
Parses the runner's command line into settings: the configuration file, the declared flags, the
repeatable {lit}`--set` and {lit}`--filter`, and the {lit}`list` subcommand with its filters.
-/
def parseOptions (args : List String) : Except String Options := do
  let (sets, filters, rest) ← takeRepeatable args
  match (runnerCmd "" fun _ => pure 0).parse rest with
  | .error e => .error e.kind.msg
  | .ok (_, parsed) => optionsOfParsed parsed sets filters

/-- Whether a character can appear unquoted in a word for a POSIX shell. -/
private def shellSafe (c : Char) : Bool :=
  c.isAlphanum || "_-./:=@%+,".contains c

/-- A word quoted for a POSIX shell: as it is when that is safe, and in single quotes otherwise. -/
def shellQuote (s : String) : String :=
  if !s.isEmpty && s.all shellSafe then s
  else "'" ++ s.replace "'" "'\\''" ++ "'"

/-- Where a run's reporters send their output. -/
structure Sinks where
  /-- Receives each line of the events file. -/
  event : Json → IO Unit := fun _ => pure ()
  /-- Receives each line of the human-readable report. -/
  line : String → IO Unit := fun _ => pure ()

/-- The dispatcher: the state of the run, behind a lock that every event passes through. -/
structure Dispatcher where
  /-- The state. -/
  state : Std.Mutex State
  /-- Where actions go. -/
  sinks : Sinks

/-- Handles one event under the dispatcher's lock, calling the reporters before it returns. -/
def Dispatcher.dispatch (d : Dispatcher) (ev : Event) : IO Unit :=
  d.state.atomically do
    let (s, actions) := step (← get) ev
    set s
    for a in actions do
      match a with
      | .event j => d.sinks.event j
      | .print l => d.sinks.line l

/-- The dispatcher's current state. -/
def Dispatcher.get (d : Dispatcher) : IO State :=
  d.state.atomically MonadState.get

/--
The processes of a run that are running, and whether the run has been cancelled. Every process
starts under the lock, after a check of the cancellation. Once the run is cancelled, every later
start is refused.
-/
structure Registry where
  /-- Whether the run has been cancelled, and the groups that are running. -/
  state : Std.Mutex (Bool × Array Group)

/-- A registry with nothing running. -/
def Registry.new : BaseIO Registry := do
  return { state := ← Std.Mutex.new (false, #[]) }

/--
Starts a process with {name}`start` and records it. When the run has been cancelled, the result is
{lean}`none` and {name}`start` is skipped.
-/
def Registry.start (r : Registry) (start : IO Group) : IO (Option Group) :=
  r.state.atomically do
    let (cancelled, groups) ← get
    if cancelled then return none
    let g ← start
    set (cancelled, groups.push g)
    return some g

/-- Forgets a process that the run has finished with. -/
def Registry.release (r : Registry) (g : Group) : IO Unit :=
  r.state.atomically (modify fun (c, gs) => (c, gs.filter (·.pid != g.pid)))

/-- Whether the run has been cancelled. -/
def Registry.cancelled (r : Registry) : IO Bool :=
  r.state.atomically (return (← get).1)

/--
Cancels the run: every later start is refused, every running group is asked to terminate, and the
groups whose first process is still running after {name}`graceMs` milliseconds are killed. The parts
of the run that started the processes wait for them.
-/
def Registry.cancel (r : Registry) (graceMs : Nat) : IO Unit := do
  let groups ← r.state.atomically do
    let (_, gs) ← get
    set (true, gs)
    return gs
  for g in groups do g.terminate
  let deadline := (← IO.monoMsNow) + graceMs
  repeat
    let live ← (← r.state.atomically (return (← get).2)).filterM (·.armed.get)
    if live.isEmpty || (← IO.monoMsNow) ≥ deadline then break
    IO.sleep pollMs
  for g in (← r.state.atomically (return (← get).2)) do g.kill

/-- What the parts of a run share. -/
structure RunContext where
  /-- The configuration. -/
  config : Config
  /-- The options. -/
  opts : Options
  /-- The run's seed. -/
  runSeed : Nat
  /-- The run's identifier, which every test executable receives as {lit}`ERRATA_RUN_ID`. -/
  runId : String := ""
  /-- A directory for the result files of the run. -/
  dir : System.FilePath
  /-- The dispatcher. -/
  dispatcher : Dispatcher
  /-- The processes that are running, and whether the run has been cancelled. -/
  registry : Registry
  /-- How long a test executable may take to list its tests, in milliseconds. -/
  listTimeoutMs : Nat := defaultTimeoutMs
  /-- How long a listing that ran past its timeout has before it is killed, in milliseconds. -/
  listGracePeriodMs : Nat := defaultGracePeriodMs

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
The environment variables that every test executable receives. {lit}`LEAN_ABORT_ON_PANIC` is
{lit}`1`, so a panic ends the process that panicked, and {lit}`ERRATA_RUN_ID` is the run's
identifier, the same for every process of one run.
-/
def RunContext.env (ctx : RunContext) (exe : ExecutableConfig) : Array (String × Option String) :=
  #[("LEAN_ABORT_ON_PANIC", some "1"), (lifelineVariable, some "1"),
      ("ERRATA_RUN_ID", some ctx.runId)] ++
    (ctx.config.errataDir?.map fun d => #[("ERRATA_DIR", some d)]).getD #[] ++
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

/--
Runs a command in a process group of its own, with the listing's timeout and grace period, and
returns its exit code with what it wrote to standard output and standard error. The exit code is
{lean}`none` when it timed out. The whole result is {lean}`none` when the run has been cancelled.
-/
def runListing (ctx : RunContext) (exe : ExecutableConfig) (args : Array String) :
    IO (Option (Option UInt32 × String × String)) := do
  let some cmd := exe.command[0]? | throw <| .userError "the command is empty"
  let some g ← ctx.registry.start
      (spawnGroup cmd (exe.command.extract 1 exe.command.size ++ args) exe.cwd? (ctx.env exe))
    | return none
  let out ← IO.mkRef ""
  let err ← IO.mkRef ""
  let outTask ← IO.asTask (prio := .dedicated)
    (forwardLines g.child.stdout fun l => out.modify (· ++ l))
  let errTask ← IO.asTask (prio := .dedicated)
    (forwardLines g.child.stderr fun l => err.modify (· ++ l))
  let finished ← g.waitAtMost ctx.listTimeoutMs
  unless finished do discard <| g.terminateGraceKill ctx.listGracePeriodMs
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
def listExecutable (ctx : RunContext) (idx : Nat) (exe : ExecutableConfig) :
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
    | return fail s!"it did not finish within {ctx.listTimeoutMs}ms"
  unless code == 0 do
    return match signalOfExitCode? code with
      | some s => fail s!"it was ended by signal {s} (exit code {code})"
      | none => fail s!"it exited with code {code}"
  let text ← IO.FS.readFile file
  let lines := text.splitOn "\n" |>.filter (!·.trimAscii.isEmpty)
  if lines.isEmpty then return fail "it wrote nothing to its list file"
  let mut sawProtocol := false
  let mut settings : Array SettingInfo := #[]
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
      | .test info =>
        unless sawProtocol do return fail "its list file does not begin with a protocol record"
        let some name := info.name? | return fail "its list file has a test without a name"
        -- The inventory leaves out benchmarks.
        if info.kind? == some "benchmark" then continue
        if names.contains name then return fail s!"it lists the test {name} more than once"
        names := names.insert name
        tests := tests.push {
          exeIdx := idx, name, path := info.path?.getD #[], file? := info.file?,
          line? := info.line?, description? := info.description?, tags := info.tags?.getD #[]
          settings := info.settings?.getD #[]
        }
      | _ => unless sawProtocol do
          return fail "its list file does not begin with a protocol record"
  unless sawProtocol do return fail "its list file has no protocol record"
  return .ok { settings, tests }

/-- The arguments of a test executable that runs one test. -/
def runArgs (out name : String) (settings : Array (String × String)) : Array String :=
  #["errata-run", out, name] ++ settings.map fun (k, v) => s!"setting:{k}={v}"

/--
The command that runs a test again by hand, quoted for a POSIX shell. Its records go to standard
error.
-/
def RunContext.reproduce (ctx : RunContext) (exe : ExecutableConfig) (name : String)
    (settings : Array (String × String)) : String :=
  let env : Array (String × String) :=
    #[("LEAN_ABORT_ON_PANIC", "1")] ++
    ((ctx.config.errataDir?.map fun d => #[("ERRATA_DIR", d)]).getD #[]) ++ exe.env
  let words := env.map (fun (k, v) => s!"{k}={shellQuote v}") ++
    (exe.command ++ runArgs "/dev/stderr" name settings).map shellQuote
  let cd := match exe.cwd? with | some d => s!"cd {shellQuote d} && " | none => ""
  cd ++ " ".intercalate words.toList

/--
The settings that a test executable receives for a test: the resolved values of the settings the
test takes, in the order it takes them, and {lit}`updateGolden` when golden checks rewrite their
expected files.
-/
def Resolved.arguments (r : Resolved) : Array (String × String) :=
  r.settings ++ (if r.updateGolden then #[("updateGolden", "true")] else #[])

/-- The test as the dispatcher plans it, with what it receives. -/
def RunContext.planned (ctx : RunContext) (exe : ExecutableConfig) (t : InventoryTest)
    (r : Resolved) : Planned :=
  let settings := r.arguments
  { exe := exe.name, test := t.name, path := t.path, description? := t.description?
    seed? := (r.settings.find? (·.1 == seedSetting)).map (·.2), settings
    reproduce := ctx.reproduce exe t.name settings, slowAfterMs := r.slowAfterMs }

/--
Runs one test in a process of its own, with the settings and limits resolved for it. Records from its
result file and lines from its standard output and standard error go to the dispatcher as they
arrive. Before a line of output is handed on, the result file is read up to its end, so the records
that the test wrote before that output precede it. The test is terminated at its timeout and killed
after the grace period. The run loop checks the clock after every bounded read of the result file.
Once the test executable has exited, the processes that it started have the pipe grace to release
its output pipes, and then its group is swept. A test whose mandatory setting has no value is
reported without being started. The result is {lean}`false` when the run has been cancelled and the
test was not started.
-/
def runOne (ctx : RunContext) (n : Nat) (t : InventoryTest) (r : Resolved) : IO Bool := do
  let exe := ctx.config.executables[t.exeIdx]!
  let planned := ctx.planned exe t r
  let d := ctx.dispatcher
  if let some missing := r.missing[0]? then
    d.dispatch (.testStarted planned)
    d.dispatch (.testEnded exe.name t.name (.settingMissing missing) 0)
    return true
  let file := ctx.dir / s!"run-{n}.jsonl"
  IO.FS.writeFile file ""
  let start ← IO.monoMsNow
  let ended (exit : Exit) : IO Unit := do
    d.dispatch (.testEnded exe.name t.name exit ((← IO.monoMsNow) - start))
  let spawned ←
    try
      let some cmd := exe.command[0]? | throw <| .userError "the command is empty"
      let g? ← ctx.registry.start <|
        spawnGroup cmd
          (exe.command.extract 1 exe.command.size ++ runArgs file.toString t.name planned.settings)
          exe.cwd? (ctx.env exe)
      pure (Except.ok g?)
    catch e => pure (.error (toString e))
  let g ← match spawned with
    | .ok none => return false
    | .ok (some g) =>
      d.dispatch (.testStarted planned)
      pure g
    | .error e =>
      d.dispatch (.testStarted planned)
      ended (.spawnFailed e)
      return true
  let tail ← Tail.open file
  let onFileLine (bytes : ByteArray) : IO Unit := do
    let line := decodeLine bytes
    if line.trimAscii.isEmpty then return
    match Protocol.Record.parseLine line with
    | .ok (some (json, record)) => d.dispatch (.record exe.name t.name json record)
    | .ok none => pure ()
    | .error e => d.dispatch (.unreadable exe.name t.name e)
  let fileLock ← Std.Mutex.new ()
  let pollFile : IO Bool := fileLock.atomically (tail.poll onFileLine)
  let forward (stream : String) (line : String) : IO Unit :=
    fileLock.atomically do
      -- The file is read to its end, a bounded read at a time, so that the records written before
      -- this line precede it. Reading stops at the test's timeout, which the run loop enforces.
      repeat
        if (← IO.monoMsNow) ≥ start + r.timeoutMs then break
        unless ← tail.poll onFileLine do break
      d.dispatch (.captured exe.name t.name stream line (← Protocol.nowMs))
  let outTask ← IO.asTask (prio := .dedicated) (forwardLines g.child.stdout (forward "stdout"))
  let errTask ← IO.asTask (prio := .dedicated) (forwardLines g.child.stderr (forward "stderr"))
  let mut timedOut : Option (Nat × Bool) := none
  repeat
    let read ← pollFile
    if (← g.tryWait).isSome then break
    let elapsed := (← IO.monoMsNow) - start
    if elapsed ≥ r.timeoutMs then
      let killed ← g.terminateGraceKill r.gracePeriodMs
      timedOut := some (elapsed, killed)
      break
    unless read do IO.sleep pollMs
  let code ← g.wait
  -- What a test that timed out wrote is read for at most the grace period more.
  let deadline? ← if timedOut.isSome then
      pure (some ((← IO.monoMsNow) + r.gracePeriodMs))
    else pure none
  fileLock.atomically (tail.finish onFileLine deadline?)
  releasePipes g [outTask, errTask]
  ctx.registry.release g
  let exit := match timedOut with
    | some (ms, killed) => Exit.timedOut ms killed
    | none => .exited code
  ended exit
  return true

/-- A value as {lit}`--list` shows it, quoted so that an empty value shows. -/
private def showValue (v : String) : String := v.quote

/--
Prints what {lit}`--list` shows: every setting the test executables declare, with its description
and its default; the tests that the filters select, each with its file and line, its tags, and the
values it receives; and the mandatory settings that nothing gives a value, with the tests that need
them. A seed derived from a run seed that the command line leaves to chance is shown as derived.
-/
def printInventory (ctx : RunContext) (listings : Array Listing)
    (selected : Array (InventoryTest × Resolved)) : IO Unit := do
  let line := ctx.dispatcher.sinks.line
  line "Settings:"
  let mut shown : Std.HashSet String := {}
  for l in listings do
    for s in l.settings do
      if shown.contains s.name then continue
      shown := shown.insert s.name
      let dflt := match s.default? with | some d => s!" (default {showValue d})" | none => ""
      line s!"  {s.name}{dflt}"
      if let some d := s.description? then
        line ("\n".intercalate ((d.trimAscii.copy.splitOn "\n").map ("      " ++ ·)))
  line "Tests:"
  let mut exe? : Option Nat := none
  let mut missing : Array (String × String) := #[]
  for (t, r) in selected do
    if exe? != some t.exeIdx then
      exe? := some t.exeIdx
      line s!"  {ctx.config.executables[t.exeIdx]!.name}"
    let loc := match t.file?, t.line? with
      | some f, some l => s!"  ({f}:{l})"
      | some f, none => s!"  ({f})"
      | _, _ => ""
    let tags := if t.tags.isEmpty then "" else s!"  [{", ".intercalate t.tags.toList}]"
    line s!"    {t.name}{loc}{tags}"
    if let some d := t.description? then
      line ("\n".intercalate ((d.trimAscii.copy.splitOn "\n").map ("        " ++ ·)))
    for (k, v) in r.settings do
      -- A seed derived from a random run seed differs in every run, so its value says nothing.
      if k == seedSetting && r.derivedSeed && ctx.opts.seed.isNone then
        line s!"        {k}: derived from the run's seed"
      else
        line s!"        {k} = {showValue v}"
    for m in r.missing do
      line s!"        {m}: no value"
      missing := missing.push (m, t.name)
  unless missing.isEmpty do
    line "Mandatory settings without a value:"
    for (m, t) in missing do
      line s!"  {m}, which {t} needs"

/--
The configuration's filters, parsed: the ones that select the tests to run, and each override's.
The command line's filters select when there are any, and otherwise the profile's default filter, or
the configuration's. The result is the messages of the filters that do not parse.
-/
def parseFilters (config : Config) (opts : Options) (profile : Profile) :
    Except (Array String) (Array SourcedFilter × Array (SourcedFilter × Override)) := do
  let mut errors := #[]
  let mut selecting := #[]
  if opts.filters.isEmpty then
    if let some f := profile.defaultFilter? <|> config.defaultFilter? then
      match SourcedFilter.parse f.text f.source with
      | .ok sf => selecting := selecting.push sf
      | .error e => errors := errors.push e
  else
    for f in opts.filters do
      match SourcedFilter.parse f (.argument "--filter") with
      | .ok sf => selecting := selecting.push sf
      | .error e => errors := errors.push e
  let mut overrides := #[]
  for o in profile.overrides do
    match SourcedFilter.parse o.filter.text o.filter.source with
    | .ok sf => overrides := overrides.push (sf, o)
    | .error e => errors := errors.push e
  if errors.isEmpty then return (selecting, overrides) else throw errors

/--
Asks every test executable for its inventory, in parallel. The result is each executable's listing,
or {lean}`none` when one could not list, which the dispatcher has been told.
-/
def listAll (ctx : RunContext) : IO (Option (Array Listing)) := do
  let d := ctx.dispatcher
  let listings ← ctx.config.executables.mapIdxM fun i exe =>
    IO.asTask (prio := .dedicated) (listExecutable ctx i exe)
  let mut out := #[]
  let mut listed := true
  for task in listings do
    match ← IO.wait task with
    | .ok (.ok l) => out := out.push l
    | .ok (.error msg) =>
      listed := false
      d.dispatch (.issue { isError := true, message := msg })
    | .error e =>
      listed := false
      d.dispatch (.issue { isError := true, message := s!"a test executable could not list: {e}" })
  return if listed then some out else none

/--
Runs the tests of every test executable in the configuration, reporting to {name}`sinks` as the run
proceeds, and returns the report. The events file's lines and the human-readable report's lines go
to the sinks; the report files are the caller's to write. The {lit}`protocol` line of the events
file is sent first.

A filter with a syntax error, an unknown profile, or a profile's {lit}`jobs` above one ends the run
before the List phase. The List phase lists every executable, then checks the configuration against
the inventory: a value that the command line gives to a setting that no executable declares is an
error, and one that the profile gives is a warning; the filters are evaluated, with a warning for
each atom and each filter that selects nothing. The configuration's filters draw these warnings only
when the run has every test executable of the package. The Run phase runs the selected tests in
inventory order.
-/
def execute (config : Config) (opts : Options) (sinks : Sinks)
    (registry : Option Registry := none) : IO RunReport := do
  let runSeed ← match opts.seed with
    | some s => pure s
    | none => IO.rand 0 (2 ^ 32 - 1)
  let runId ← newRunId
  let dispatcher : Dispatcher :=
    { state := ← Std.Mutex.new { human := { verbosity := opts.verbosity }, wfail := opts.wfail }
      sinks }
  sinks.event (Json.mkObj [("type", Json.str "protocol"), ("version", ToJson.toJson Protocol.version),
    ("run_id", Json.str runId)])
  let registry ← match registry with
    | some r => pure r
    | none => Registry.new
  let d := dispatcher
  let finish : IO RunReport := do
    -- A listing runs nothing, so it has no counts to sum up.
    d.dispatch (.ended (← Protocol.nowMs) (summary := !opts.list))
    let s ← d.get
    return { results := s.results, issues := s.issues, seed := runSeed, runId }
  for w in config.warnings do
    d.dispatch (.issue { isError := false, message := w })
  let some profile := config.profile? opts.profile
    | d.dispatch (.issue { isError := true, message := s!"the configuration has no profile named \
        {opts.profile}; its profiles are {", ".intercalate config.profileNames.toList}" })
      finish
  if let some jobs := profile.jobs? then
    unless jobs == 1 do
      d.dispatch (.issue { isError := true, message := s!"the profile {profile.name} sets jobs to \
        {jobs}: only 1 is supported" })
      return ← finish
  let (selecting, overrides) ← match parseFilters config opts profile with
    | .ok fs => pure fs
    | .error errors =>
      for e in errors do d.dispatch (.issue { isError := true, message := e })
      return ← finish
  IO.FS.withTempDir fun dir => do
    let ctx : RunContext := {
      config, opts, runSeed, runId, dir, dispatcher, registry
      listTimeoutMs := opts.timeoutMs? <|> profile.timeoutMs? |>.getD defaultTimeoutMs
      listGracePeriodMs := opts.gracePeriodMs? <|> profile.gracePeriodMs? |>.getD defaultGracePeriodMs
    }
    d.dispatch (.phase "List" (← Protocol.nowMs))
    let some listings ← listAll ctx | finish
    let inventory := listings.flatMap (·.tests)
    if inventory.isEmpty then
      d.dispatch (.issue { isError := true, message := "no tests were discovered" })
    let exeName (t : InventoryTest) : String := config.executables[t.exeIdx]!.name
    let resolution : ResolutionContext := {
      sets := opts.sets, profile, overrides, timeoutMs? := opts.timeoutMs?
      gracePeriodMs? := opts.gracePeriodMs?, updateGolden := opts.updateGolden, runSeed
    }
    -- A value that the command line gives to a setting that nothing declares stops the run. One that
    -- the configuration gives is a warning, since a profile serves the executables of every library
    -- and a run may select some of them.
    let declared := listings.flatMap (·.settings.map (·.name))
    let undeclared := resolution.undeclared declared
    let names := declared.foldl (init := #[]) fun acc n => if acc.contains n then acc else acc.push n
    for u in undeclared do
      d.dispatch (.issue { isError := u.commandLine, message := s!"{u.place} gives the setting \
        {u.name} a value, and no test executable of this run declares it; the declared settings are \
        {if names.isEmpty then "none" else ", ".intercalate names.toList}" })
    if undeclared.any (·.commandLine) then return ← finish
    let records := inventory.map fun t => t.record (exeName t)
    let exes := config.executables.map (·.name)
    -- The configuration's filters serve every executable of the package, so they are checked
    -- against the inventory only when the run has all of them. The command line's always are.
    let fromCommandLine := !opts.filters.isEmpty
    let checked :=
      (if fromCommandLine || !config.partialSelection then selecting else #[]) ++
      (if config.partialSelection then #[] else overrides.map (·.1))
    for f in checked do
      for w in f.warnings records exes do
        d.dispatch (.issue { isError := false, message := w })
    let chosen := Filter.unionOf (selecting.map (·.expr))
    let selected := inventory.filterMap fun t =>
      if chosen.eval (t.record (exeName t)) then
        some (t, resolution.resolve (exeName t) listings[t.exeIdx]!.settings t)
      else none
    if opts.list then
      printInventory ctx listings selected
    else
      d.dispatch (.phase "Run" (← Protocol.nowMs))
      for h : i in [0 : selected.size] do
        let (t, r) := selected[i]
        unless ← runOne ctx i t r do break
    finish

/-- Writes the report files that the options ask for. -/
def writeReports (opts : Options) (report : RunReport) : IO Unit := do
  let write (path? : Option String) (render : RunReport → String) : IO Unit := do
    if let some path := path? then writeFile path (render report)
  write opts.junitPath junitReport
  write opts.jsonPath jsonReport
  write opts.markdownPath markdownReport

/--
The {lit}`list` subcommand: lists every test executable, then prints one line per test that the
filters select, in inventory order: the executable, the name, the file and line, and the tags. No
filter selects every test, and several are joined by union. The result is the exit code: {lit}`1`
when a filter has a syntax error or an executable cannot list, and {lit}`0` otherwise.
-/
def listSubcommand (config : Config) (opts : Options) (filters : Array String)
    (registry : Registry) : IO UInt32 := do
  let mut parsed := #[]
  for (f, i) in filters.zipIdx do
    match SourcedFilter.parse f (.argument s!"list filter {i + 1}") with
    | .ok sf => parsed := parsed.push sf
    | .error e =>
      IO.eprintln s!"error: {e}"
      return 1
  let dispatcher : Dispatcher := {
    state := ← Std.Mutex.new { human := { verbosity := .silent } }
    sinks := {}
  }
  IO.FS.withTempDir fun dir => do
    let ctx : RunContext := {
      config, opts, runSeed := 0, runId := ← newRunId, dir, dispatcher, registry
      listTimeoutMs := opts.timeoutMs?.getD defaultTimeoutMs
      listGracePeriodMs := opts.gracePeriodMs?.getD defaultGracePeriodMs
    }
    let some listings ← listAll ctx
      | for issue in (← dispatcher.get).issues do IO.eprintln s!"error: {issue.message}"
        return 1
    let chosen := Filter.unionOf (parsed.map (·.expr))
    let tests := listings.flatMap (·.tests)
    let rows := tests.filterMap fun t =>
      let exe := config.executables[t.exeIdx]!.name
      if chosen.eval (t.record exe) then
        let loc := match t.file?, t.line? with
          | some f, some l => s!"{f}:{l}"
          | some f, none => f
          | _, _ => "-"
        let tags := if t.tags.isEmpty then "" else s!"[{", ".intercalate t.tags.toList}]"
        some #[exe, t.name, loc, tags]
      else none
    -- The columns are padded to their widest entry, with two spaces between them.
    let width (i : Nat) : Nat := rows.foldl (fun w r => max w (r[i]!.length)) 0
    let widths := #[width 0, width 1, width 2]
    for r in rows do
      let cols := (List.range 3).map fun i => r[i]!.pushn ' ' (widths[i]! - r[i]!.length)
      IO.println ("  ".intercalate (cols ++ [r[3]!]) |>.trimAsciiEnd.copy)
    return 0

/--
Runs the tests as {name}`execute` does, with the human-readable report on standard output and the
events in the file that the options name, then writes the report files and prints the run's issues.
The result is the exit code: {lit}`0` when every test passed and no issue is an error. A cancelled
run writes no report files and returns {lit}`1`.
-/
def executeAndWrite (config : Config) (opts : Options)
    (registry : Option Registry := none) : IO UInt32 := do
  let registry ← match registry with
    | some r => pure r
    | none => Registry.new
  let events? ← opts.eventsPath.mapM fun p => do
    if let some parent := (p : System.FilePath).parent then IO.FS.createDirAll parent
    IO.FS.Handle.mk p .append
  let sinks : Sinks := {
    event := fun j => do
      if let some h := events? then
        h.putStr (j.compress ++ "\n")
        h.flush
    line := fun l => do
      IO.println l
      (← IO.getStdout).flush
  }
  let report ← execute config opts sinks registry
  -- A cancelled run writes no reports.
  if ← registry.cancelled then return 1
  writeReports opts report
  for issue in report.issues do
    IO.eprintln s!"{issue.level}: {issue.message}"
  return if report.succeeded then 0 else 1

/--
Cancels the run once the runner's lifeline, its standard input, closes: every later start is
refused, and the running processes are terminated and, after the grace period, killed. The driver
holds the other end of that pipe, which closes when the driver exits, however it exits. After the
cancellation, the run loop has the grace period, four pipe graces, and two more seconds to end, and
then the runner exits with {lit}`1`.
-/
def exitWhenStdinCloses (parentIn : IO.FS.Stream) (registry : Registry) (graceMs : Nat) :
    IO Unit := do
  repeat
    if (← parentIn.getLine).isEmpty then break
  try IO.eprintln "errata-runner: standard input closed, so the run ends" catch _ => pure ()
  registry.cancel graceMs
  -- The run loop reaps the processes and ends what they left holding their pipes; this bounds how
  -- long that may take.
  IO.sleep (graceMs + 4 * pipeGraceMs + 2000).toUInt32
  try (← IO.getStdout).flush catch _ => pure ()
  IO.Process.forceExit 1

/--
The runner's entry point: {lit}`errata-runner <config.json> [options]`, or
{lit}`errata-runner <config.json> list [FILTER]...`. The configuration's {lit}`invocation`, when it
has one, names the command in the usage message. When {lit}`ERRATA_LIFELINE` is {lit}`1` in its
environment, the runner watches its standard input and cancels the run when it closes.
-/
def main (args : List String) : IO UInt32 := do
  let invocation ← do
    match args with
    | path :: _ =>
      if path.startsWith "-" then pure none
      else
        try pure (← Config.load path).invocation?
        catch _ => pure none
    | [] => pure none
  let (sets, filters, rest) ← match takeRepeatable args with
    | .ok r => pure r
    | .error msg =>
      IO.eprintln s!"error: {msg}"
      return 1
  let cmd := runnerCmd (invocation.getD "errata-runner CONFIG") fun parsed => do
    let opts ←
      match optionsOfParsed parsed sets filters with
      | .ok opts => pure opts
      | .error msg =>
        IO.eprintln s!"error: {msg}"
        return 1
    let config ←
      try Config.load opts.configPath
      catch e =>
        IO.eprintln s!"error: {e}"
        return 1
    let registry ← Registry.new
    let grace := opts.gracePeriodMs?.getD defaultGracePeriodMs
    -- The driver sets the variable when it gives the runner a standard input to watch.
    if (← IO.getEnv lifelineVariable) == some "1" then
      let _ ← IO.asTask (prio := .dedicated) (exitWhenStdinCloses (← IO.getStdin) registry grace)
    let code ← match opts.listFilters? with
      | some fs => listSubcommand config opts fs registry
      | none => executeAndWrite config opts (some registry)
    try (← IO.getStdout).flush catch _ => pure ()
    try (← IO.getStderr).flush catch _ => pure ()
    -- The thread that reads standard input runs until the pipe closes, and a Lean program that
    -- returns from `main` waits for its threads, so the runner ends the process itself.
    IO.Process.forceExit code.toUInt8
  cmd.validate rest
