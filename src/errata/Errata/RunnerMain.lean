/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The runner: it lists the tests of every test executable in its configuration, runs each test in a
process of its own under a timeout, merges what the test executable reported with what it observed
from outside, and writes the reports.
-/
module

public import Errata.RunnerConfig
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
  /-- Lists the tests without running them. -/
  list : Bool := false
  /-- How long a test may run before it is terminated, in milliseconds. -/
  timeoutMs : Nat := 10 * 60 * 1000
  /-- How long a terminated test has before it is killed, in milliseconds. -/
  gracePeriodMs : Nat := 10 * 1000
  /-- Options for the tests themselves, passed to every test as settings, in order. -/
  testOptions : Array (String × String) := #[]
deriving Repr, Inhabited

/--
Parses a duration: a natural number followed by {lit}`ms`, {lit}`s`, or {lit}`m`. The result is in
milliseconds.
-/
def parseDuration (s : String) : Except String Nat :=
  let s := s.trimAscii.copy
  let num (digits : String) (scale : Nat) : Except String Nat :=
    match digits.toNat? with
    | some n => .ok (n * scale)
    | none => .error s!"invalid duration '{s}': expected a number followed by ms, s, or m"
  if let some d := s.dropSuffix? "ms" then num d.copy 1
  else if let some d := s.dropSuffix? "s" then num d.copy 1000
  else if let some d := s.dropSuffix? "m" then num d.copy 60000
  else .error s!"invalid duration '{s}': expected a number followed by ms, s, or m"

/--
Parses the options passed through to the tests: {lit}`--name value` and {lit}`--name=value` pairs,
in order. The {lit}`--name value` form takes the next token as the value when that token does not
begin with {lit}`-`; a value that does uses the {lit}`--name=value` form. A name alone has the empty
value. Any other token is rejected.
-/
partial def parseTestOptions (tokens : List String) : Except String (Array (String × String)) :=
  go #[] tokens
where
  go (acc : Array (String × String)) : List String → Except String (Array (String × String))
    | [] => .ok acc
    | tok :: rest =>
      match tok.dropPrefix? "--" with
      | none =>
        .error s!"unexpected argument '{tok}': test options are `--name value` or `--name=value`"
      | some name =>
        match name.copy.splitOn "=" with
        | [] => unreachable! -- `splitOn` always returns at least one element
        | [n] =>
          if n.isEmpty then .error s!"unexpected argument: {tok}"
          else match rest with
            | value :: rest' =>
              if value.startsWith "-" then go (acc.push (n, "")) rest
              else go (acc.push (n, value)) rest'
            | [] => .ok (acc.push (n, ""))
        | n :: valueParts =>
          if n.isEmpty then .error s!"unexpected argument: {tok}"
          else go (acc.push (n, "=".intercalate valueParts)) rest

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
      list;                    "List the tests without running them."
      timeout : String;        "How long a test may run before it is stopped, such as 90s or 10m (10m)."
      "grace-period" : String; "How long a stopped test has before it is killed (10s)."

    ARGS:
      config : String;         "The configuration file that the driver writes."
      ...testOption : String;  "Options for the tests themselves; see below."

    EXTENSIONS:
      longDescription "Options for the tests themselves go after a `--` separator, as \
        `--name value` or `--name=value`. Write a value that begins with `-` as `--name=value`. \
        Each test receives them as settings."
  ]

/-- The value of a path-valued flag, when it is present; a present but empty path is an error. -/
private def pathFlag (p : Cli.Parsed) (name : String) : Except String (Option String) :=
  match p.flag? name with
  | none => .ok none
  | some f => if f.value.isEmpty then .error s!"--{name} expects a path" else .ok (some f.value)

/-- The settings that the runner passes to the Lean harness for its own options. -/
private def reservedTestOptions : List String := ["seed", "updateGolden"]

/-- Interprets a parsed command line as runner settings. -/
def optionsOfParsed (p : Cli.Parsed) : Except String Options := do
  let verbosity : Verbosity :=
    if p.hasFlag "verbose-docs" then .superVerbose
    else if p.hasFlag "verbose-all" then .verbose
    else if p.hasFlag "verbose" then .quiet
    else .silent
  let jobs := (p.flag? "jobs" |>.map (·.as! Nat)).getD 1
  if jobs == 0 then throw "--jobs 0 is invalid: at least one test must be able to run"
  unless jobs == 1 do
    throw s!"--jobs {jobs}: only --jobs 1 is supported"
  let timeoutMs ← match p.flag? "timeout" with
    | some f => parseDuration f.value
    | none => pure (10 * 60 * 1000)
  if timeoutMs == 0 then throw "--timeout must be longer than zero"
  let gracePeriodMs ← match p.flag? "grace-period" with
    | some f => parseDuration f.value
    | none => pure (10 * 1000)
  let testOptions ← parseTestOptions (p.variableArgsAs! String).toList
  if let some (name, _) := testOptions.find? (reservedTestOptions.contains ·.1) then
    throw s!"the test option --{name} is reserved for the runner's own options"
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
    jobs, list := p.hasFlag "list", timeoutMs, gracePeriodMs, testOptions
  }

/--
Parses the runner's command line into settings: the configuration file, the declared flags, then
any options for the tests themselves after a {lit}`--` separator.
-/
def parseOptions (args : List String) : Except String Options :=
  match (runnerCmd "" fun _ => pure 0).parse args with
  | .error e => .error e.kind.msg
  | .ok (_, parsed) => optionsOfParsed parsed

/-- Whether a character can appear unquoted in a word for a POSIX shell. -/
private def shellSafe (c : Char) : Bool :=
  c.isAlphanum || "_-./:=@%+,".contains c

/-- A word quoted for a POSIX shell: as it is when that is safe, and in single quotes otherwise. -/
def shellQuote (s : String) : String :=
  if !s.isEmpty && s.all shellSafe then s
  else "'" ++ s.replace "'" "'\\''" ++ "'"

/--
The seed that a test receives: the run's seed mixed with the executable's and the test's names, so
that each test draws from its own stream and adding a test changes no other test's seed.
-/
def testSeed (runSeed : Nat) (exe test : String) : Nat :=
  (mixHash (mixHash (hash runSeed) (hash exe)) (hash test)).toNat

/-- A test in the inventory. -/
structure InventoryTest where
  /-- The position of the test's executable in the configuration. -/
  exeIdx : Nat
  /-- The test's name. -/
  name : String
  /-- The components of the test's name. -/
  path : Array String := #[]
  /-- The file that defines the test. -/
  file? : Option String := none
  /-- The line of its declaration. -/
  line? : Option Nat := none
  /-- The test's description. -/
  description? : Option String := none
deriving Repr, Inhabited

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
  /-- A directory for the result files of the run. -/
  dir : System.FilePath
  /-- The dispatcher. -/
  dispatcher : Dispatcher
  /-- The processes that are running, and whether the run has been cancelled. -/
  registry : Registry

/--
The environment variable that asks a process to treat its standard input as its lifeline, and to
end when it closes.
-/
def lifelineVariable : String := "ERRATA_LIFELINE"

/--
The environment variables that every test executable receives. {lit}`LEAN_ABORT_ON_PANIC` is
{lit}`1`, so a panic ends the process that panicked.
-/
def RunContext.env (ctx : RunContext) (exe : ExecutableConfig) : Array (String × Option String) :=
  #[("LEAN_ABORT_ON_PANIC", some "1"), (lifelineVariable, some "1")] ++
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
Runs a command in a process group of its own, with the run's timeout and grace period, and returns
its exit code with what it wrote to standard output and standard error. The exit code is
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
  let finished ← g.waitAtMost ctx.opts.timeoutMs
  unless finished do discard <| g.terminateGraceKill ctx.opts.gracePeriodMs
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
Asks one test executable for its inventory. The result is its tests, or the message that says why
it could not list them.
-/
def listExecutable (ctx : RunContext) (idx : Nat) (exe : ExecutableConfig) :
    IO (Except String (Array InventoryTest)) := do
  let file := ctx.dir / s!"list-{idx}.jsonl"
  IO.FS.writeFile file ""
  let listing ←
    try runListing ctx exe #["errata-list", file.toString]
    catch e => return .error (listFailure exe s!"it could not be started: {e}" "" "")
  let some (code?, stdout, stderr) := listing
    | return .error (listFailure exe "the run was cancelled" "" "")
  let fail (why : String) := Except.error (listFailure exe why stdout stderr)
  let some code := code?
    | return fail s!"it did not finish within {ctx.opts.timeoutMs}ms"
  unless code == 0 do
    return match signalOfExitCode? code with
      | some s => fail s!"it was ended by signal {s} (exit code {code})"
      | none => fail s!"it exited with code {code}"
  let text ← IO.FS.readFile file
  let lines := text.splitOn "\n" |>.filter (!·.trimAscii.isEmpty)
  if lines.isEmpty then return fail "it wrote nothing to its list file"
  let mut sawProtocol := false
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
      | .test info =>
        unless sawProtocol do return fail "its list file does not begin with a protocol record"
        let some name := info.name? | return fail "its list file has a test without a name"
        -- The inventory leaves out benchmarks.
        if info.kind? == some "benchmark" then continue
        if names.contains name then return fail s!"it lists the test {name} more than once"
        names := names.insert name
        tests := tests.push {
          exeIdx := idx, name, path := info.path?.getD #[], file? := info.file?,
          line? := info.line?, description? := info.description?
        }
      | _ => unless sawProtocol do
          return fail "its list file does not begin with a protocol record"
  unless sawProtocol do return fail "its list file has no protocol record"
  return .ok tests

/-- The settings that a test receives: its seed, the runner's own options, and the test options. -/
def RunContext.settingsFor (ctx : RunContext) (exe : ExecutableConfig) (t : InventoryTest) :
    Nat × Array (String × String) :=
  let seed := testSeed ctx.runSeed exe.name t.name
  let flags := if ctx.opts.updateGolden then #[("updateGolden", "true")] else #[]
  (seed, #[("seed", toString seed)] ++ flags ++ ctx.opts.testOptions)

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
Runs one test in a process of its own. Records from its result file and lines from its standard
output and standard error go to the dispatcher as they arrive. Before a line of output is handed on,
the result file is read up to its end, so the records that the test wrote before that output precede
it. The test is terminated at its timeout and killed after the grace period. The run loop checks the
clock after every bounded read of the result file. Once the test executable has exited, the
processes that it started have the pipe grace to release its output pipes, and then its group is
swept. The result is {lean}`false` when the run has been cancelled and the test was not started.
-/
def runOne (ctx : RunContext) (n : Nat) (t : InventoryTest) : IO Bool := do
  let exe := ctx.config.executables[t.exeIdx]!
  let (seed, settings) := ctx.settingsFor exe t
  let planned : Planned := {
    exe := exe.name, test := t.name, path := t.path, description? := t.description?, seed, settings
    reproduce := ctx.reproduce exe t.name settings
  }
  let d := ctx.dispatcher
  let file := ctx.dir / s!"run-{n}.jsonl"
  IO.FS.writeFile file ""
  let start ← IO.monoMsNow
  let ended (exit : Exit) : IO Unit := do
    d.dispatch (.testEnded exe.name t.name exit ((← IO.monoMsNow) - start))
  let spawned ←
    try
      let some cmd := exe.command[0]? | throw <| .userError "the command is empty"
      let g? ← ctx.registry.start <|
        spawnGroup cmd (exe.command.extract 1 exe.command.size ++ runArgs file.toString t.name settings)
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
        if (← IO.monoMsNow) ≥ start + ctx.opts.timeoutMs then break
        unless ← tail.poll onFileLine do break
      d.dispatch (.captured exe.name t.name stream line (← Protocol.nowMs))
  let outTask ← IO.asTask (prio := .dedicated) (forwardLines g.child.stdout (forward "stdout"))
  let errTask ← IO.asTask (prio := .dedicated) (forwardLines g.child.stderr (forward "stderr"))
  let mut timedOut : Option (Nat × Bool) := none
  repeat
    let read ← pollFile
    if (← g.tryWait).isSome then break
    let elapsed := (← IO.monoMsNow) - start
    if elapsed ≥ ctx.opts.timeoutMs then
      let killed ← g.terminateGraceKill ctx.opts.gracePeriodMs
      timedOut := some (elapsed, killed)
      break
    unless read do IO.sleep pollMs
  let code ← g.wait
  -- What a test that timed out wrote is read for at most the grace period more.
  let deadline? ← if timedOut.isSome then
      pure (some ((← IO.monoMsNow) + ctx.opts.gracePeriodMs))
    else pure none
  fileLock.atomically (tail.finish onFileLine deadline?)
  releasePipes g [outTask, errTask]
  ctx.registry.release g
  let exit := match timedOut with
    | some (ms, killed) => Exit.timedOut ms killed
    | none => .exited code
  ended exit
  return true

/-- Prints the inventory, for {lit}`--list`. -/
def printInventory (ctx : RunContext) (tests : Array InventoryTest) : IO Unit := do
  let mut exe? : Option Nat := none
  for t in tests do
    if exe? != some t.exeIdx then
      exe? := some t.exeIdx
      ctx.dispatcher.sinks.line (ctx.config.executables[t.exeIdx]!.name)
    let loc := match t.file?, t.line? with
      | some f, some l => s!"  ({f}:{l})"
      | some f, none => s!"  ({f})"
      | _, _ => ""
    ctx.dispatcher.sinks.line s!"  {t.name}{loc}"
    if let some d := t.description? then
      ctx.dispatcher.sinks.line ("\n".intercalate ((d.splitOn "\n").map ("      " ++ ·)))

/--
Runs the tests of every test executable in the configuration, reporting to {name}`sinks` as the run
proceeds, and returns the report. The events file's lines and the human-readable report's lines go
to the sinks; the report files are the caller's to write. The {lit}`protocol` line of the events
file is sent first.
-/
def execute (config : Config) (opts : Options) (sinks : Sinks)
    (registry : Option Registry := none) : IO RunReport := do
  let runSeed ← match opts.seed with
    | some s => pure s
    | none => IO.rand 0 (2 ^ 32 - 1)
  let dispatcher : Dispatcher :=
    { state := ← Std.Mutex.new { human := { verbosity := opts.verbosity }, wfail := opts.wfail }
      sinks }
  sinks.event (Json.mkObj [("type", Json.str "protocol"), ("version", ToJson.toJson Protocol.version)])
  let registry ← match registry with
    | some r => pure r
    | none => Registry.new
  IO.FS.withTempDir fun dir => do
    let ctx : RunContext := { config, opts, runSeed, dir, dispatcher, registry }
    let d := dispatcher
    for w in config.warnings do
      d.dispatch (.issue { isError := false, message := w })
    d.dispatch (.phase "List" (← Protocol.nowMs))
    let listings ← config.executables.mapIdxM fun i exe =>
      IO.asTask (prio := .dedicated) (listExecutable ctx i exe)
    let mut inventory : Array InventoryTest := #[]
    let mut listed := true
    for task in listings do
      match ← IO.wait task with
      | .ok (.ok tests) => inventory := inventory ++ tests
      | .ok (.error msg) =>
        listed := false
        d.dispatch (.issue { isError := true, message := msg })
      | .error e =>
        listed := false
        d.dispatch (.issue { isError := true, message := s!"a test executable could not list: {e}" })
    if listed then
      if inventory.isEmpty then
        d.dispatch (.issue { isError := true, message := "no tests were discovered" })
      if opts.list then
        printInventory ctx inventory
      else
        d.dispatch (.phase "Run" (← Protocol.nowMs))
        for h : i in [0 : inventory.size] do
          unless ← runOne ctx i inventory[i] do break
    d.dispatch (.ended (← Protocol.nowMs))
    let s ← d.get
    return { results := s.results, issues := s.issues, seed := runSeed }

/-- Writes the report files that the options ask for. -/
def writeReports (opts : Options) (report : RunReport) : IO Unit := do
  let write (path? : Option String) (render : RunReport → String) : IO Unit := do
    if let some path := path? then writeFile path (render report)
  write opts.junitPath junitReport
  write opts.jsonPath jsonReport
  write opts.markdownPath markdownReport

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
The runner's entry point: {lit}`errata-runner <config.json> [options] [-- test options]`. The
configuration's {lit}`invocation`, when it has one, names the command in the usage message. When
{lit}`ERRATA_LIFELINE` is {lit}`1` in its environment, the runner watches its standard input and
cancels the run when it closes.
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
  let cmd := runnerCmd (invocation.getD "errata-runner CONFIG") fun parsed => do
    let opts ←
      match optionsOfParsed parsed with
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
    -- The driver sets the variable when it gives the runner a standard input to watch.
    if (← IO.getEnv lifelineVariable) == some "1" then
      let _ ← IO.asTask (prio := .dedicated)
        (exitWhenStdinCloses (← IO.getStdin) registry opts.gracePeriodMs)
    let code ← executeAndWrite config opts (some registry)
    try (← IO.getStdout).flush catch _ => pure ()
    try (← IO.getStderr).flush catch _ => pure ()
    -- The thread that reads standard input runs until the pipe closes, and a Lean program that
    -- returns from `main` waits for its threads, so the runner ends the process itself.
    IO.Process.forceExit code.toUInt8
  cmd.validate args
