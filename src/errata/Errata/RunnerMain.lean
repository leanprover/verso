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
public import Errata.Scheduler
public import Errata.ProcessControl
public import Errata.CommandLine
public import Errata.Progress
public import Std.Sync.Mutex
import all Errata.FS

public section

set_option linter.missingDocs true
set_option doc.verso true

open Lean (Json ToJson)

namespace Errata.Runner

open ProcessControl

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
  /--
  The progress display, when the run keeps one. The dispatcher updates its frame as tests and
  fixture phases start and end, with the lines of the event in one batch, and clears it at the end
  of the run. The {name}`Sinks.line` of a run with a display is the display's
  {name}`Progress.Display.print`.
  -/
  progress? : Option Progress.Display := none

/--
Handles one event under the dispatcher's lock, calling the reporters before it returns. With a
progress display, the display follows the event, and the end of the run clears it before the
summary.
-/
def Dispatcher.dispatch (d : Dispatcher) (ev : Event) : IO Unit :=
  d.state.atomically do
    let before ← get
    let (s, actions) := step before ev
    set s
    let report : IO Unit :=
      for a in actions do
        match a with
        | .event j => d.sinks.event j
        | .print l => d.sinks.line l
    match d.progress? with
    | none => report
    | some p =>
      if ev matches .ended .. then p.clear
      -- Only the starts and ends of tests and fixture phases change the frame.
      if ev matches .testStarted _ | .testEnded .. then
        let fresh := s.results.extract before.results.size s.results.size
        let now ← IO.monoMsNow
        p.batch do
          report
          p.update (·.after ev fresh now)
      else report

/-- The dispatcher's current state. -/
def Dispatcher.get (d : Dispatcher) : IO State :=
  d.state.atomically MonadState.get

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
What a lifeline that outlives its invocation serves: a fixture, whose setup's lifeline lasts until
its teardown ends, or a test, whose prepares' lifelines last until the test ends.
-/
inductive LifelineOwner where
  /-- The fixture of that name in the executable of that name. -/
  | fixture (exe name : String)
  /-- The test of that name in the executable of that name. -/
  | test (exe name : String)
deriving BEq

/--
The lifelines that the run holds after their invocations have ended, each the write end of an
invocation's standard input, with what it serves. Processes that setups and prepares start inherit
their lifelines and end when those close. Lifelines close when they are released, and the run
closes those still held when it ends.
-/
structure Lifelines where
  /-- The held lifelines. -/
  held : Std.Mutex (Array (LifelineOwner × IO.FS.Handle))

/-- A new set of held lifelines, empty. -/
def Lifelines.new : BaseIO Lifelines := return { held := ← Std.Mutex.new #[] }

/-- Holds {name}`h` until what {name}`owner` names ends. -/
def Lifelines.hold (l : Lifelines) (owner : LifelineOwner) (h : IO.FS.Handle) : BaseIO Unit :=
  l.held.atomically (modify (·.push (owner, h)))

/-- Drops the lifelines held for {name}`owner`, which closes them. -/
def Lifelines.release (l : Lifelines) (owner : LifelineOwner) : BaseIO Unit :=
  l.held.atomically (modify (·.filter (·.1 != owner)))

/-- Drops every held lifeline, which closes it. The run calls this when it ends. -/
def Lifelines.closeAll (l : Lifelines) : BaseIO Unit :=
  l.held.atomically (set (#[] : Array (LifelineOwner × IO.FS.Handle)))

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
  /-- The lifelines of setups and prepares, held after their invocations end. -/
  lifelines : Lifelines
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
The arguments after a test's or a fixture phase's name: its settings, the values of its fixtures,
and its thread grant.
-/
def invocationArgs (settings fixtures : Array (String × String)) (threads : Nat) :
    Array String :=
  settings.map (fun (k, v) => s!"setting:{k}={v}") ++
    fixtures.map (fun (k, v) => s!"fixture:{k}={v}") ++ #[s!"threads:{threads}"]

/-- The arguments of a test executable that runs one test. -/
def runArgs (out name : String) (settings : Array (String × String))
    (fixtures : Array (String × String) := #[]) (threads : Nat := 1) : Array String :=
  #["errata-run", out, name] ++ invocationArgs settings fixtures threads

/-- The arguments of a test executable that runs one phase of a fixture. -/
def fixtureArgs (out name : String) (phase : FixturePhase) (settings : Array (String × String))
    (fixtures : Array (String × String) := #[]) (threads : Nat := 1) : Array String :=
  #["errata-fixture", out, name, phase.name] ++ invocationArgs settings fixtures threads

/--
The command that runs a chain of invocations by hand, quoted for a POSIX shell: the executable
with the invocations separated by {lit}`;` arguments. Their records go to standard error, and
{lit}`LEAN_NUM_THREADS` is {name}`threads?`, the thread grant of the invocation that the chain
reproduces when the run bounded it, and absent otherwise.
-/
def RunContext.reproduceChain (ctx : RunContext) (exe : ExecutableConfig)
    (links : Array (Array String)) (threads? : Option Nat := none) : String :=
  let env : Array (String × String) :=
    #[("LEAN_ABORT_ON_PANIC", "1")] ++
    ((ctx.config.errataDir?.map fun d => #[("ERRATA_DIR", d)]).getD #[]) ++ exe.env ++
    ((threads?.map fun n => #[("LEAN_NUM_THREADS", toString n)]).getD #[])
  let chain := links.foldl (init := #[]) fun acc l =>
    (if acc.isEmpty then acc else acc.push ";") ++ l
  let words := env.map (fun (k, v) => s!"{k}={shellQuote v}") ++
    (exe.command ++ chain).map shellQuote
  let cd := match exe.cwd? with | some d => s!"cd {shellQuote d} && " | none => ""
  cd ++ " ".intercalate words.toList

/--
The command that runs a test again by hand, quoted for a POSIX shell. Its records go to standard
error.
-/
def RunContext.reproduce (ctx : RunContext) (exe : ExecutableConfig) (name : String)
    (settings : Array (String × String)) : String :=
  ctx.reproduceChain exe #[runArgs "/dev/stderr" name settings]

/--
The settings that a test executable receives for a test: the resolved values of the settings the
test takes, in the order it takes them, and {lit}`Errata.updateGolden` with the value {lit}`true`
when golden checks rewrite their expected files.
-/
def Resolved.arguments (r : Resolved) : Array (String × String) :=
  if !r.updateGolden then r.settings
  else if r.settings.any (·.1 == updateGoldenSetting) then
    r.settings.map fun (k, v) => if k == updateGoldenSetting then (k, "true") else (k, v)
  else r.settings.push (updateGoldenSetting, "true")

/-- The test as the dispatcher plans it, with what it receives. -/
def RunContext.planned (ctx : RunContext) (exe : ExecutableConfig) (t : InventoryTest)
    (r : Resolved) : Planned :=
  let settings := r.arguments
  { exe := exe.name, test := t.name, path := t.path, description? := t.description?
    seed? := (r.settings.find? (·.1 == seedSetting)).map (·.2), settings
    reproduce := ctx.reproduce exe t.name settings, slowAfterMs := r.slowAfterMs }

/-- A test or a fixture's phase, as the runner starts it in a process of its own. -/
structure Invocation where
  /-- The test executable. -/
  exe : ExecutableConfig
  /-- What the dispatcher knows of it. -/
  planned : Planned
  /-- The arguments for a result file at the given path. -/
  args : String → Array String
  /-- The thread grant. -/
  threads : Nat := 1
  /--
  Whether {lit}`LEAN_NUM_THREADS` bounds its runtime to the grant, as it does when tests run
  concurrently.
  -/
  boundRuntime : Bool := false
  /-- How long it may run, in milliseconds. -/
  timeoutMs : Nat
  /-- How long it has after it is terminated, in milliseconds. -/
  gracePeriodMs : Nat

/-- How a test's or a fixture phase's process ended, as the scheduler learns it. -/
structure JobEnd where
  /-- How the process ended. -/
  exit : Exit
  /-- Whether the outcome is a pass. -/
  succeeded : Bool
  /-- The value that a setup wrote, when it wrote one. -/
  value? : Option String := none

/-- Tells the dispatcher that an invocation ended, and returns how it ended for the scheduler. -/
def RunContext.ended (ctx : RunContext) (inv : Invocation) (exit : Exit) (durationMs : Nat)
    (value? : Option String := none) : IO JobEnd := do
  let p := inv.planned
  ctx.dispatcher.dispatch (.testEnded p.exe p.test p.key exit durationMs)
  let results := (← ctx.dispatcher.get).results
  let own? := results.findRev? fun r =>
    r.exe == p.exe && r.test == p.test && r.kind == p.kind && r.path == p.path &&
      r.resultPath.isEmpty
  return { exit, succeeded := own?.any (·.outcome.isPass), value? }

/--
Settles the lifelines when an invocation ends. Setups' lifelines are held until their fixtures'
teardowns end, and prepares' until the tests they prepared end. When a teardown ends, the lifeline
held for its fixture closes, and when a test ends, those held for it close; their own lifelines
close with them. The run closes the lifelines still held when it ends, with
{name}`Lifelines.closeAll`.
-/
def RunContext.keepLifeline (ctx : RunContext) (inv : Invocation) (g : Group) : BaseIO Unit := do
  let p := inv.planned
  match p.kind, p.phase?, p.preparedTest? with
  | .fixture, some .setup, _ => ctx.lifelines.hold (.fixture p.exe p.test) g.child.stdin
  | .fixture, some .prepare, some test => ctx.lifelines.hold (.test p.exe test) g.child.stdin
  | .fixture, some .teardown, _ => ctx.lifelines.release (.fixture p.exe p.test)
  | .test, _, _ => ctx.lifelines.release (.test p.exe p.test)
  | _, _, _ => pure ()

/--
Watches an invocation's process from its start to its end, as {lit}`RunContext.launch` describes,
and returns how it ended.
-/
def RunContext.watch (ctx : RunContext) (inv : Invocation) (g : Group) (file : System.FilePath)
    (start : Nat) : IO JobEnd := do
  let d := ctx.dispatcher
  let p := inv.planned
  let value ← IO.mkRef (none : Option String)
  let tail ← Tail.open file
  let onFileLine (bytes : ByteArray) : IO Unit := do
    let line := decodeLine bytes
    if line.trimAscii.isEmpty then return
    match Protocol.Record.parseLine line with
    | .ok (some (json, record)) =>
      if let .value text? := record then value.set (some (text?.getD ""))
      d.dispatch (.record p.exe p.test p.key json record)
    | .ok none => pure ()
    | .error e => d.dispatch (.unreadable p.exe p.test p.key e)
  let fileLock ← Std.Mutex.new ()
  let pollFile : IO Bool := fileLock.atomically (tail.poll onFileLine)
  let forward (stream : String) (line : String) : IO Unit :=
    fileLock.atomically do
      -- The file is read to its end, a bounded read at a time, so that the records written before
      -- this line precede it. Reading stops at the timeout, which the run loop enforces.
      repeat
        if (← IO.monoMsNow) ≥ start + inv.timeoutMs then break
        unless ← tail.poll onFileLine do break
      d.dispatch (.captured p.exe p.test p.key stream line (← Protocol.nowMs))
  let outTask ← IO.asTask (prio := .dedicated) (forwardLines g.child.stdout (forward "stdout"))
  let errTask ← IO.asTask (prio := .dedicated) (forwardLines g.child.stderr (forward "stderr"))
  let mut timedOut : Option (Nat × Bool) := none
  repeat
    let read ← pollFile
    if (← g.tryWait).isSome then break
    let elapsed := (← IO.monoMsNow) - start
    if elapsed ≥ inv.timeoutMs then
      let killed ← g.terminateGraceKill inv.gracePeriodMs
      timedOut := some (elapsed, killed)
      break
    unless read do IO.sleep pollMs
  let code ← g.wait
  -- If the invocation timed out, what it wrote is read for at most the grace period more.
  let deadline? ← if timedOut.isSome then
      pure (some ((← IO.monoMsNow) + inv.gracePeriodMs))
    else pure none
  fileLock.atomically (tail.finish onFileLine deadline?)
  releasePipes g [outTask, errTask]
  ctx.registry.release g
  ctx.keepLifeline inv g
  let exit := match timedOut with
    | some (ms, killed) => Exit.timedOut ms killed
    | none => .exited code
  ctx.ended inv exit ((← IO.monoMsNow) - start) (← value.get)

/--
Starts a test or a fixture's phase in a process of its own, with the settings, fixtures' values,
and limits resolved for it, and returns a task that ends with the process, or {lean}`none` when the
run has been cancelled and nothing was started. Records from its result file and lines from its
standard output and standard error go to the dispatcher as they arrive. Before a line of output is
handed on, the result file is read up to its end, so the records that it wrote before that output
precede it. It is terminated at its timeout and killed after the grace period; the watch checks the
clock after every bounded read of the result file. Once the test executable has exited, the
processes that it started have the pipe grace to release its output pipes, and then its process
group is swept. If the invocation bounds its runtime, as it does when the slot pool has more than
one slot, the environment sets {lit}`LEAN_NUM_THREADS` to the thread grant, and the processes that
the test executable starts inherit it; with one slot, the environment leaves the variable unset,
whatever the runner's own environment holds, and the sole process and what it starts use the
machine. {name}`n` numbers the result file. Teardowns, which {name}`teardown` marks, start after a
cancellation too.
-/
def RunContext.launch (ctx : RunContext) (inv : Invocation) (n : Nat) (teardown : Bool := false) :
    IO (Option (Task JobEnd)) := do
  let d := ctx.dispatcher
  let exe := inv.exe
  let file := ctx.dir / s!"run-{n}.jsonl"
  IO.FS.writeFile file ""
  let start ← IO.monoMsNow
  let env := ctx.env exe ++
    #[("LEAN_NUM_THREADS", if inv.boundRuntime then some (toString inv.threads) else none)]
  let spawned ←
    try
      let some cmd := exe.command[0]? | throw <| .userError "the command is empty"
      let g? ← ctx.registry.start (afterCancel := teardown)
        (allowanceMs := inv.timeoutMs + inv.gracePeriodMs + 4 * pipeGraceMs) <|
        spawnGroup cmd (exe.command.extract 1 exe.command.size ++ inv.args file.toString) exe.cwd?
          env
      pure (Except.ok g?)
    catch e => pure (.error (toString e))
  match spawned with
  | .ok none => return none
  | .error e =>
    d.dispatch (.testStarted inv.planned)
    return some (.pure (← ctx.ended inv (.spawnFailed e) 0))
  | .ok (some g) =>
    d.dispatch (.testStarted inv.planned)
    let watching : BaseIO JobEnd := do
      match ← (ctx.watch inv g file start).toBaseIO with
      | .ok e => pure e
      | .error e =>
        pure { exit := .spawnFailed s!"the runner lost the process: {e}", succeeded := false }
    return some (← BaseIO.asTask (prio := .dedicated) watching)

/-- The tests and fixtures of a run, as the scheduler numbers them. -/
structure Plan where
  /-- The number of hardware-thread slots. -/
  pool : Nat
  /-- The selected tests, each with what it receives, in queue order. -/
  tests : Array (InventoryTest × Resolved)
  /--
  The fixtures that the tests need, each with its executable's position and what its phases
  receive, each after the fixtures it takes.
  -/
  fixtures : Array (Nat × InventoryFixture × Resolved)
  /-- The scheduler's view of the tests. -/
  testSpecs : Array Scheduler.TestSpec
  /-- The scheduler's view of the fixtures. -/
  fixtureSpecs : Array Scheduler.FixtureSpec

/--
The plan of a run with {name}`pool` slots and the {name}`selected` tests: the fixtures that the
tests need, directly or through other fixtures, in the order their executables list them, resolved
as {name}`resolution` says.
-/
def RunContext.fixturePlan (ctx : RunContext) (pool : Nat) (listings : Array Listing)
    (resolution : ResolutionContext) (selected : Array (InventoryTest × Resolved)) : Plan :=
    Id.run do
  let mut index : Std.HashMap (Nat × String) Nat := {}
  let mut fixtures := #[]
  let mut specs : Array Scheduler.FixtureSpec := #[]
  for h : e in [0 : listings.size] do
    let listing := listings[e]
    let mut needed : Std.HashSet String := selected.foldl (init := {}) fun s (t, _) =>
      if t.exeIdx == e then t.fixtures.foldl (init := s) (·.insert ·.name) else s
    -- Each fixture's own fixtures are listed before it, so one pass from the last reaches all.
    for f in listing.fixtures.reverse do
      if needed.contains f.name then
        needed := f.fixtures.foldl (init := needed) (·.insert ·)
    let exe := ctx.config.executables[e]!.name
    for f in listing.fixtures do
      unless needed.contains f.name do continue
      let r := resolution.resolveFixture exe listing.settings f
      index := index.insert (e, f.name) fixtures.size
      fixtures := fixtures.push (e, f, r)
      specs := specs.push {
        deps := f.fixtures.filterMap (fun d => index.get? (e, d)), threads := f.threads?.getD 1
        missing? := r.missing[0]? }
  let testSpecs := selected.map fun (t, r) => {
    fixtures := t.fixtures.filterMap fun d => (index.get? (t.exeIdx, d.name)).map (·, d.exclusive)
    threads := t.threads?.getD 1, missing? := r.missing[0]? : Scheduler.TestSpec }
  return { pool, tests := selected, fixtures, testSpecs, fixtureSpecs := specs }

/--
Warnings about settings that a test receives with one value and a fixture it needs, directly or
through other fixtures, with another, as an override that selects the test can make happen.
-/
def Plan.settingConflicts (plan : Plan) : Array String := Id.run do
  let mut out := #[]
  for h : t in [0 : plan.tests.size] do
    let (test, r) := plan.tests[t]
    for f in Scheduler.closureOf plan.fixtureSpecs (plan.testSpecs[t]!.fixtures.map (·.1)) do
      let (_, fixture, fr) := plan.fixtures[f]!
      for (k, v) in fr.settings do
        if let some (_, mine) := r.settings.find? (·.1 == k) then
          unless mine == v do
            out := out.push s!"the test {test.name} receives the setting {k} as {mine.quote}, and \
              its fixture {fixture.name} received it as {v.quote}"
  return out

/--
Whether the run bounds each process's runtime threads with {lit}`LEAN_NUM_THREADS`, which it does
when its slot pool has more than one slot, so that tests run concurrently.
-/
def Plan.boundsRuntime (plan : Plan) : Bool := plan.pool > 1

/-- The grant of a request of {name}`n` threads in the plan's pool. -/
def Plan.grant (plan : Plan) (n : Nat) : Nat := max 1 (min n plan.pool)

/-- The thread grant of a test: its request, one when it asks for none, within the pool. -/
def Plan.testThreads (plan : Plan) (t : Nat) : Nat :=
  plan.grant (plan.tests[t]!.1.threads?.getD 1)

/--
The thread grant of a fixture's phases: its request, one when it asks for none, within the pool.
-/
def Plan.fixtureThreads (plan : Plan) (f : Nat) : Nat :=
  plan.grant (plan.fixtures[f]!.2.1.threads?.getD 1)

/-- Fixtures' values, given by the fixtures' positions, by the fixtures' names. -/
def Plan.namedValues (plan : Plan) (values : Array (Nat × String)) : Array (String × String) :=
  values.map fun (i, v) => (plan.fixtures[i]!.2.1.name, v)

/-- The arguments of one phase of a fixture, with the values of the given fixtures. -/
def Plan.phaseArgs (plan : Plan) (out : String) (f : Nat) (phase : FixturePhase)
    (values : Array (Nat × String)) : Array String :=
  let (_, fixture, r) := plan.fixtures[f]!
  fixtureArgs out fixture.name phase r.settings (plan.namedValues values) (plan.fixtureThreads f)

/-- The arguments of a test, with the values of the given fixtures. -/
def Plan.testArgs (plan : Plan) (out : String) (t : Nat) (values : Array (Nat × String)) :
    Array String :=
  let (test, r) := plan.tests[t]!
  runArgs out test.name r.arguments (plan.namedValues values) (plan.testThreads t)

/--
The command that reproduces a job by hand: the setups of the fixtures it needs, each after those it
takes, then the prepares and the test for a test, or the job itself for a fixture's phase, then the
teardowns, in the reverse order of the setups. The chain supplies the fixtures' values.
-/
def RunContext.reproduceJob (ctx : RunContext) (plan : Plan) (job : Scheduler.Job) : String :=
  let out := "/dev/stderr"
  let (exeIdx, roots, middle, threads) : Nat × Array Nat × Array (Array String) × Nat :=
    match job with
    | .test t =>
      let direct := plan.testSpecs[t]!.fixtures.map (·.1)
      (plan.tests[t]!.1.exeIdx, direct,
        direct.map (plan.phaseArgs out · .prepare #[]) ++ #[plan.testArgs out t #[]],
        plan.testThreads t)
    | .setup f | .teardown f => (plan.fixtures[f]!.1, #[f], #[], plan.fixtureThreads f)
    | .prepare f _ =>
      (plan.fixtures[f]!.1, #[f], #[plan.phaseArgs out f .prepare #[]], plan.fixtureThreads f)
  let closure := Scheduler.closureOf plan.fixtureSpecs roots
  let links := closure.map (plan.phaseArgs out · .setup #[]) ++ middle ++
    closure.reverse.map (plan.phaseArgs out · .teardown #[])
  ctx.reproduceChain ctx.config.executables[exeIdx]! links
    (if plan.boundsRuntime then some threads else none)

/-- What the dispatcher knows of a job before it runs. -/
def RunContext.plannedJob (ctx : RunContext) (plan : Plan) (job : Scheduler.Job) : Planned :=
  let reproduce := ctx.reproduceJob plan job
  match job with
  | .test t =>
    let (test, r) := plan.tests[t]!
    { ctx.planned ctx.config.executables[test.exeIdx]! test r with reproduce }
  | .setup f | .prepare f _ | .teardown f =>
    let (e, fixture, r) := plan.fixtures[f]!
    let (key, path, phase, preparedTest?) := match job with
      | .prepare _ t =>
        let name := plan.tests[t]!.1.name
        (s!"prepare {name}", #[fixture.name, "prepare", name], FixturePhase.prepare, some name)
      | .teardown _ => ("teardown", #[fixture.name, "teardown"], .teardown, none)
      | _ => ("setup", #[fixture.name, "setup"], .setup, none)
    { exe := ctx.config.executables[e]!.name, test := fixture.name, key, kind := .fixture, path
      phase? := some phase, preparedTest?
      description? := fixture.description?, settings := r.settings
      seed? := (r.settings.find? (·.1 == seedSetting)).map (·.2), reproduce
      slowAfterMs := r.slowAfterMs }

/-- The key of the results of a job: its test's, or its fixture's phase's. -/
def RunContext.jobKey (ctx : RunContext) (plan : Plan) (job : Scheduler.Job) : Result.Key :=
  match job with
  | .test t =>
    let test := plan.tests[t]!.1
    { exe := ctx.config.executables[test.exeIdx]!.name, test := test.name }
  | .setup f | .prepare f _ | .teardown f =>
    let (e, fixture, _) := plan.fixtures[f]!
    let phase := match job with
      | .prepare _ t => #[fixture.name, "prepare", plan.tests[t]!.1.name]
      | .teardown _ => #[fixture.name, "teardown"]
      | _ => #[fixture.name, "setup"]
    { exe := ctx.config.executables[e]!.name, test := fixture.name, phase }

/-- The plan with its tests in the order that {name}`positions` gives by their current positions. -/
def Plan.reorder (plan : Plan) (positions : Array Nat) : Plan :=
  { plan with
    tests := positions.map (plan.tests[·]!), testSpecs := positions.map (plan.testSpecs[·]!) }

/--
The key of each test's group in the scheduling order: the executables and names of the fixtures that
the test takes, directly or through other fixtures, or the test's own executable and name when it
takes none. Each test without fixtures is thus a group of its own.
-/
def RunContext.groupKeys (ctx : RunContext) (plan : Plan) : Array String :=
  (List.range plan.tests.size).toArray.map fun t =>
    let closure := Scheduler.closureOf plan.fixtureSpecs (plan.testSpecs[t]!.fixtures.map (·.1))
    if closure.isEmpty then
      let key := ctx.jobKey plan (.test t)
      s!"test\x00{key.exe}\x00{key.test}"
    else
      "fixtures" ++ String.join (closure.toList.map fun f =>
        let (e, fixture, _) := plan.fixtures[f]!
        s!"\x00{ctx.config.executables[e]!.name}\x00{fixture.name}")

/--
The fixtures among {name}`fs` in the order of their teardowns: each after every fixture among them
that takes it, and otherwise the earliest in the plan first.
-/
def Plan.teardownOrder (plan : Plan) (fs : Array Nat) : Array Nat := Id.run do
  let mut left := fs.qsort (· < ·)
  let mut out := #[]
  while !left.isEmpty do
    let ready? := left.find? fun f => !left.any fun g => plan.fixtureSpecs[g]!.deps.contains f
    -- Fixtures come after the fixtures they take, so the latest one left is always ready.
    let f := ready?.getD left.back!
    out := out.push f
    left := left.filter (· != f)
  return out

/--
The keys of the tests and fixtures' phases of a plan in the order of the JUnit report. The tests
stand in the plan's order, each after the prepares of its fixtures, in the order it names them.
Fixtures' setups stand before the first test that needs the fixture, directly or through other
fixtures, each after the setups of the fixtures it takes. Their teardowns stand after the last such
test, each before the teardowns of the fixtures it takes. A plan in the inventory's order gives the
inventory's order.
-/
def RunContext.reportOrder (ctx : RunContext) (plan : Plan) : Array Result.Key := Id.run do
  let closures := plan.testSpecs.map fun spec =>
    Scheduler.closureOf plan.fixtureSpecs (spec.fixtures.map (·.1))
  let mut firstUser : Std.HashMap Nat Nat := {}
  let mut lastUser : Std.HashMap Nat Nat := {}
  for h : t in [0 : closures.size] do
    for f in closures[t] do
      firstUser := firstUser.insertIfNew f t
      lastUser := lastUser.insert f t
  let mut out := #[]
  for h : t in [0 : closures.size] do
    for f in closures[t] do
      if firstUser.get? f == some t then out := out.push (ctx.jobKey plan (.setup f))
    for (f, _) in plan.testSpecs[t]!.fixtures do
      out := out.push (ctx.jobKey plan (.prepare f t))
    out := out.push (ctx.jobKey plan (.test t))
    let ending := closures[t].filter (lastUser.get? · == some t)
    for f in plan.teardownOrder ending do
      out := out.push (ctx.jobKey plan (.teardown f))
  return out

/-- The invocation that runs a job, with the values of the fixtures it receives. -/
def RunContext.invocation (ctx : RunContext) (plan : Plan) (job : Scheduler.Job)
    (values : Array (Nat × String)) : Invocation :=
  let planned := ctx.plannedJob plan job
  match job with
  | .test t =>
    let (test, r) := plan.tests[t]!
    { exe := ctx.config.executables[test.exeIdx]!, planned
      args := (plan.testArgs · t values), threads := plan.testThreads t
      boundRuntime := plan.boundsRuntime
      timeoutMs := r.timeoutMs, gracePeriodMs := r.gracePeriodMs }
  | .setup f | .prepare f _ | .teardown f =>
    let (e, _, r) := plan.fixtures[f]!
    let phase : FixturePhase := match job with
      | .prepare .. => .prepare
      | .teardown _ => .teardown
      | _ => .setup
    { exe := ctx.config.executables[e]!, planned
      args := (plan.phaseArgs · f phase values), threads := plan.fixtureThreads f
      boundRuntime := plan.boundsRuntime
      timeoutMs := r.timeoutMs, gracePeriodMs := r.gracePeriodMs }

/--
Runs the plan's tests and the phases of their fixtures, as the scheduler directs: it starts each job
that the scheduler asks for, reports the tests and setups that it asks to report without running,
and tells it of each process that ends, until it ends the run. Once the run has been cancelled, the
scheduler learns of it before the next command, starts no more tests, and tears down the fixtures
whose setups were invoked. When nothing runs and the scheduler has not ended the run, the tests it
never started are named in a run-level error.
-/
def RunContext.runScheduled (ctx : RunContext) (plan : Plan) : IO Unit := do
  let d := ctx.dispatcher
  let mut sched := Scheduler.State.init plan.pool plan.testSpecs plan.fixtureSpecs
  let (s, first) := Scheduler.step sched .begin
  sched := s
  let mut queue := first
  let mut running : Array (Nat × Scheduler.Job × Task JobEnd) := #[]
  let mut launched := 0
  let mut toldCancelled := false
  repeat
    let mut finished := false
    let mut i := 0
    while i < queue.size do
      -- A cancellation reaches the scheduler before the next command, so it starts only teardowns.
      if !toldCancelled && (← ctx.registry.cancelled) then
        toldCancelled := true
        let (s, more) := Scheduler.step sched .cancelled
        sched := s
        queue := queue ++ more
      let cmd := queue[i]!
      i := i + 1
      match cmd with
      | .finish => finished := true
      | .skip job reason =>
        let p := ctx.plannedJob plan job
        let exit : Exit := match reason with
          | .settingMissing s => .settingMissing s
          | .fixtureFailed f phase => .fixtureFailed plan.fixtures[f]!.2.1.name phase
        d.dispatch (.testStarted p)
        d.dispatch (.testEnded p.exe p.test p.key exit 0)
      | .spawn job _ values =>
        let teardown := job matches .teardown _
        match ← ctx.launch (ctx.invocation plan job values) launched teardown with
        | none =>
          -- The run was cancelled after the scheduler asked for the job, which never started.
          toldCancelled := true
          let (s, more) := Scheduler.step sched .cancelled
          let (s, more') := Scheduler.step s (.exited job false)
          sched := s
          queue := queue ++ more ++ more'
        | some task =>
          running := running.push (launched, job, task)
          launched := launched + 1
    queue := #[]
    if finished then break
    let tasks := running.toList.map fun (n, _, task) => task.map (n, ·)
    let (n, e) ← match tasks with
      | [] =>
        -- Nothing runs and the scheduler has not ended the run, so the tests left never start.
        let pending := (List.range plan.tests.size).filter fun t =>
          !(sched.testStatus[t]! matches .done)
        let names := pending.map (plan.tests[·]!.1.name)
        d.dispatch (.issue { isError := true, message := s!"the scheduler stopped with nothing \
          running before these tests ran: {", ".intercalate names}" })
        break
      | t :: ts => IO.waitAny (t :: ts)
    let some (_, job, _) := running.find? (·.1 == n) | break
    running := running.filter (·.1 != n)
    if let .setup f := job then
      if e.succeeded then
        let (s, _) := Scheduler.step sched (.valueProduced f (e.value?.getD ""))
        sched := s
    let event : Scheduler.Event := match e.exit with
      | .timedOut .. => .timedOut job
      | _ => .exited job e.succeeded
    let (s, more) := Scheduler.step sched event
    sched := s
    queue := more

/-- A value as a listing shows it, quoted so that an empty value shows. -/
private def showValue (v : String) : String := v.quote

/-- Text indented line by line. -/
private def indented (indent text : String) : String :=
  "\n".intercalate ((text.trimAscii.copy.splitOn "\n").map (indent ++ ·))

/-- The selected tests, gathered by test executable in inventory order. -/
private def byExecutable (selected : Array (InventoryTest × Resolved)) :
    Array (Nat × Array (InventoryTest × Resolved)) :=
  selected.foldl (init := #[]) fun acc (t, r) =>
    match acc.back? with
    | some (i, group) =>
      if i == t.exeIdx then acc.pop.push (i, group.push (t, r)) else acc.push (t.exeIdx, #[(t, r)])
    | none => #[(t.exeIdx, #[(t, r)])]

/--
Prints the selected tests in nextest's human format: each test executable's name and a colon, then
its selected tests, indented by four spaces. With {name}`verbose`, the settings that the test
executables declare come first when there are any, with their descriptions and defaults, and then
the fixtures they declare when there are any, with their descriptions, the threads they ask for, and
the settings and the fixtures they take;
each test is followed by its file and line, its tags, its description, the values it receives, and
the fixtures it uses; and the mandatory settings that nothing gives a value come last, with the
tests that need them. Seeds derived from a run seed that the command line leaves to chance are
shown as derived.
-/
def printHumanList (ctx : RunContext) (color verbose : Bool) (listings : Array Listing)
    (selected : Array (InventoryTest × Resolved)) : IO Unit := do
  let line := ctx.dispatcher.sinks.line
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
  for (idx, tests) in byExecutable selected do
    line s!"{Style.exe.paint color ctx.config.executables[idx]!.name}:"
    for (t, r) in tests do
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
        -- Seeds derived from a random run seed differ in every run, so their values say nothing.
        if k == seedSetting && r.derivedSeed && ctx.opts.seed.isNone then
          line s!"        {k}: derived from the run's seed"
        else
          line s!"        {k} = {showValue v}"
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
def printOnelineList (ctx : RunContext) (selected : Array (InventoryTest × Resolved)) :
    IO Unit := do
  let rows := selected.map fun (t, _) =>
    let loc := match t.file?, t.line? with
      | some f, some l => s!"{f}:{l}"
      | some f, none => f
      | _, _ => "-"
    let tags := if t.tags.isEmpty then "" else s!"[{", ".intercalate t.tags.toList}]"
    #[ctx.config.executables[t.exeIdx]!.name, t.name, loc, tags]
  let width (i : Nat) : Nat := rows.foldl (fun w r => max w (r[i]!.length)) 0
  let widths := #[width 0, width 1, width 2]
  for r in rows do
    let cols := (List.range 3).map fun i => r[i]!.pushn ' ' (widths[i]! - r[i]!.length)
    ctx.dispatcher.sinks.line ("  ".intercalate (cols ++ [r[3]!]) |>.trimAsciiEnd.copy)

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

/--
The selected tests as JSON: the profile, the run's seed, the number of listed tests selected and
left out, under {lit}`not-built` the names of the libraries and executables that the filters ruled
out before building, the settings that the test executables declare, and each test executable with
its selected tests and the fixtures they reach.
Each test has its name, path, file, line, tags, and description, the values it receives, the
mandatory settings without a value, whether its seed is derived from the run's, its timeout, grace
period, and slow mark in milliseconds, and the fixtures it uses, each exclusive or shared.
Each fixture has its name, description, the settings and the fixtures it takes, and the threads it
asks for.
-/
def inventoryJson (ctx : RunContext) (profile : String) (listings : Array Listing)
    (selected : Array (InventoryTest × Resolved)) (skipped : Nat) : Json := Id.run do
  let opt {α} [ToJson α] (key : String) (v? : Option α) : List (String × Json) :=
    (v?.map fun v => (key, ToJson.toJson v)).toList
  let mut settings : Array Json := #[]
  let mut seen : Std.HashSet String := {}
  for l in listings do
    for s in l.settings do
      if seen.contains s.name then continue
      seen := seen.insert s.name
      settings := settings.push <| Json.mkObj <| [("name", Json.str s.name)] ++
        opt "description" s.description? ++ opt "default" s.default?
  let testJson (t : InventoryTest) (r : Resolved) : Json := Json.mkObj <|
    [("name", Json.str t.name), ("path", ToJson.toJson t.path)] ++ opt "file" t.file? ++
    opt "line" t.line? ++ [("tags", ToJson.toJson t.tags)] ++ opt "description" t.description? ++
    [("settings", Json.mkObj (r.arguments.toList.map fun (k, v) => (k, Json.str v))),
      ("missing", ToJson.toJson r.missing), ("derived-seed", Json.bool r.derivedSeed),
      ("timeout-ms", ToJson.toJson r.timeoutMs), ("grace-period-ms", ToJson.toJson r.gracePeriodMs),
      ("slow-after-ms", ToJson.toJson r.slowAfterMs),
      ("fixtures", Json.arr (t.fixtures.map fun f =>
        Json.mkObj [("name", Json.str f.name), ("exclusive", Json.bool f.exclusive)]))]
  let fixtureJson (f : InventoryFixture) : Json := Json.mkObj <|
    [("name", Json.str f.name)] ++ opt "description" f.description? ++
    [("settings", ToJson.toJson f.settings), ("fixtures", ToJson.toJson f.fixtures)] ++
    opt "threads" f.threads?
  let groups := byExecutable selected
  let executables := ctx.config.executables.mapIdx fun i e =>
    let tests : Array (InventoryTest × Resolved) :=
      (groups.find? (·.1 == i)).map (·.2) |>.getD #[]
    let fixtures := match listings[i]? with
      | some l => reachedFixtures l (tests.map Prod.fst)
      | none => #[]
    Json.mkObj [("name", Json.str e.name), ("command", ToJson.toJson e.command),
      ("tests", Json.arr (tests.map fun (t, r) => testJson t r)),
      ("fixtures", Json.arr (fixtures.map fixtureJson))]
  return Json.mkObj [("profile", Json.str profile), ("seed", ToJson.toJson ctx.runSeed),
    ("selected", ToJson.toJson selected.size), ("skipped", ToJson.toJson skipped),
    ("not-built", ToJson.toJson ctx.config.ruledOut),
    ("settings", Json.arr settings), ("executables", Json.arr executables)]

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
The message of a run that selects no test under {lit}`--no-tests fail`.
-/
def noTestsMessage : String :=
  "no tests to run; --no-tests warn or --no-tests pass accepts a run that selects none"

/--
Runs or lists the tests of every test executable in the configuration, reporting to {name}`sinks` as
the run proceeds, and returns the report with the exit code. The events file's lines and the
human-readable report's lines go to the sinks; the report files are the caller's to write. The
{lit}`protocol` line of the events file is sent first. The human-readable report is colored when
{name}`color` is true.

Filters with syntax errors and unknown profiles end the run before the List phase. The List phase
lists every executable, then checks the configuration against the inventory: values that the
command line gives to settings that no executable declares are errors, and those that the profile
gives are warnings; the filters are evaluated, with a warning for each atom and each filter that
selects nothing. The configuration's filters draw these warnings only when the run has every test
executable of the package. The {lit}`list` command then prints the selected tests in its message
format. The Run phase runs the selected tests and the phases of the fixtures they use as the
scheduler directs, in the scheduling order as far as the fixtures' claims and the slots of the pool
allow. The scheduling order is the inventory's, or under the profile's {lit}`order = "shuffle"` the
order that {name}`Scheduler.groupedOrder` draws from the run's seed, in which tests that take the
same fixtures stand together. The JUnit report lists the tests in the inventory's order whatever the
scheduling order. The pool has the slots that {lit}`--jobs` or else the profile's {lit}`jobs` gives,
or else one per CPU available to the runner. When {name}`progress?` gives a progress display, the
run starts it as the Run phase begins, and the dispatcher keeps it up to date. However the run ends,
it closes the held lifelines and clears the progress display.
-/
def execute (config : Config) (opts : Options) (sinks : Sinks)
    (registry : Option Registry := none) (color : Bool := false)
    (progress? : Option Progress.Display := none) : IO (RunReport × UInt32) := do
  let runSeed ← match opts.seed with
    | some s => pure s
    | none => IO.rand 0 (2 ^ 32 - 1)
  let runId ← newRunId
  let listing := opts.command == .list
  -- A listing prints no results, so its reporter prints nothing of its own.
  let human : HumanReporter := { verbosity := if listing then .silent else opts.verbosity, color }
  let dispatcher : Dispatcher :=
    { state := ← Std.Mutex.new {
        human, wfail := opts.wfail, startMs := ← Protocol.nowMs, seed? := some runSeed }
      sinks, progress? }
  sinks.event (Json.mkObj [("type", Json.str "protocol"), ("version", ToJson.toJson Protocol.version),
    ("run_id", Json.str runId), ("seed", ToJson.toJson runSeed)])
  let registry ← match registry with
    | some r => pure r
    | none => Registry.new
  let d := dispatcher
  let finish (code : UInt32) (skipped? : Option (Nat × Nat × Nat) := none)
      (order : Array Result.Key := #[]) : IO (RunReport × UInt32) := do
    -- A listing runs nothing, so it has no counts to sum up.
    d.dispatch (.ended (← Protocol.nowMs) (!listing) skipped?)
    let s ← d.get
    return ({ results := s.results, issues := s.issues, seed := runSeed, runId, order }, code)
  for w in config.warnings do
    d.dispatch (.issue { isError := false, message := w })
  let some profile := config.profile? opts.profile
    | d.dispatch (.issue { isError := true, message := unknownProfile config opts.profile })
      finish ExitCode.setupError
  let (selection, overrides) ← match parseSelection config opts profile with
    | .ok fs => pure fs
    | .error (errors, code) =>
      for e in errors do d.dispatch (.issue { isError := true, message := e })
      return ← finish code
  let lifelines ← Lifelines.new
  -- However the run ends, the held lifelines close and the progress display is cleared.
  let closeRun : IO Unit := do
    lifelines.closeAll
    if let some p := progress? then p.clear
  flip tryFinally closeRun <| IO.FS.withTempDir fun dir => do
    let ctx : RunContext := {
      config, opts, runSeed, runId, dir, dispatcher, registry, lifelines
      listTimeoutMs := opts.timeoutMs? <|> profile.timeoutMs? |>.getD defaultTimeoutMs
      listGracePeriodMs := opts.gracePeriodMs? <|> profile.gracePeriodMs? |>.getD defaultGracePeriodMs
    }
    d.dispatch (.phase "List" (← Protocol.nowMs) none)
    let some listings ← listAll ctx | finish ExitCode.listFailed
    let inventory := listings.flatMap (·.tests)
    let exeName (t : InventoryTest) : String := config.executables[t.exeIdx]!.name
    let resolution : ResolutionContext := {
      sets := opts.sets, profile, overrides, timeoutMs? := opts.timeoutMs?
      fixtureTimeoutMs? := opts.fixtureTimeoutMs?, gracePeriodMs? := opts.gracePeriodMs?
      updateGolden := opts.updateGolden, runSeed
      default? := selection.default?
    }
    -- A value for `Errata.updateGolden` given as a setting stops the run.
    let golden := resolution.updateGoldenValues
    for m in golden do d.dispatch (.issue { isError := true, message := m })
    unless golden.isEmpty do return ← finish ExitCode.setupError
    -- Values that the command line gives to settings that nothing declares stop the run. Those that
    -- the configuration gives are warnings, since profiles serve the executables of every library
    -- and runs may select some of them. A run that selects only some of them reports none of these.
    let declared := listings.flatMap (·.settings.map (·.name))
    let undeclared := resolution.undeclared declared |>.filter fun u =>
      u.commandLine || !config.partialSelection
    let names := declared.foldl (init := #[]) fun acc n => if acc.contains n then acc else acc.push n
    for u in undeclared do
      d.dispatch (.issue { isError := u.commandLine, message := s!"{u.place} gives the setting \
        {u.name} a value, and no test executable of this run declares it; the declared settings are \
        {if names.isEmpty then "none" else ", ".intercalate names.toList}" })
    if undeclared.any (·.commandLine) then return ← finish ExitCode.setupError
    let records := inventory.map fun t => t.record (exeName t)
    -- An `exe(…)` is judged against every executable of the package, those that the filters ruled
    -- out before building included.
    let exes := config.executableNames
    -- The configuration's filters serve every executable of the package, so they are checked
    -- against the inventory only when the run has all of them. The command line's always are.
    let checked := selection.filters ++
      (if config.partialSelection then #[] else selection.default?.toArray ++ overrides.map (·.1))
    for f in checked do
      for w in f.warnings records exes selection.defaultSelects do
        d.dispatch (.issue { isError := false, message := w })
    let selected := inventory.filterMap fun t =>
      if selection.selects (t.record (exeName t)) then
        some (t, resolution.resolve (exeName t) listings[t.exeIdx]!.settings t)
      else none
    let skipped := inventory.size - selected.size
    if listing then
      match opts.messageFormat with
      | .human => printHumanList ctx color (opts.verbosity != .silent) listings selected
      | .oneline => printOnelineList ctx selected
      | .json => sinks.line (inventoryJson ctx profile.name listings selected skipped).compress
      | .jsonPretty => sinks.line (inventoryJson ctx profile.name listings selected skipped).pretty
      return ← finish ExitCode.ok
    if selected.isEmpty then
      match opts.noTests with
      | .fail => d.dispatch (.issue { isError := true, message := noTestsMessage })
      | .warn => d.dispatch (.issue { isError := false, message := "no tests to run" })
      | .pass => pure ()
    let pool ← match opts.jobs? <|> profile.jobs? with
      | some n => pure (max n 1)
      | none =>
        let (n, warning?) ← availableParallelism
        if let some w := warning? then d.dispatch (.issue { isError := false, message := w })
        pure n
    -- The executable column is as wide as the longest name among the executables that run tests.
    let exeWidth := selected.foldl (init := 0) fun w (t, _) => max w (exeName t).length
    d.state.atomically (modify fun s => { s with human := { s.human with exeWidth } })
    d.dispatch (.phase "Run" (← Protocol.nowMs) (some pool))
    let inventoryPlan := ctx.fixturePlan pool listings resolution selected
    for w in inventoryPlan.settingConflicts do
      d.dispatch (.issue { isError := false, message := w })
    let plan := match profile.order?.getD .default with
      | .default => inventoryPlan
      | .shuffle =>
        inventoryPlan.reorder (Scheduler.groupedOrder runSeed (ctx.groupKeys inventoryPlan))
    if let some p := progress? then p.start plan.tests.size exeWidth
    ctx.runScheduled plan
    let s ← d.get
    -- Under `--wfail`, the warning of `--no-tests warn` fails the run as `--no-tests fail` does.
    let code :=
      if selected.isEmpty && (opts.noTests == .fail || (opts.noTests == .warn && opts.wfail)) then
        ExitCode.noTestsRun
      else if s.results.all (·.outcome.isPass) && !s.issues.any (·.isError) then ExitCode.ok
      else ExitCode.testRunFailed
    finish code (skipped, config.skippedTestLibraries.size, config.skippedExecutables.size)
      (ctx.reportOrder inventoryPlan)

/--
The paths of the JUnit, JSON, and Markdown reports: the command line's, or else the profile's, which
are relative to the package's directory.
-/
def reportPaths (config : Config) (opts : Options) :
    Option String × Option String × Option String :=
  let profile? := config.profile? opts.profile
  let fromProfile (field : Profile → Option String) : Option String :=
    (profile?.bind field).map fun (p : String) =>
      match config.packageDir? with
      | some dir => (System.FilePath.mk dir / System.FilePath.mk p).toString
      | none => p
  (opts.junitPath <|> fromProfile (·.junitPath?), opts.jsonPath <|> fromProfile (·.jsonPath?),
    opts.markdownPath <|> fromProfile (·.markdownPath?))

/-- Writes the report files at the paths that {name}`reportPaths` gives. -/
def writeReports (config : Config) (opts : Options) (report : RunReport) : IO Unit := do
  let (junit?, json?, markdown?) := reportPaths config opts
  let write (path? : Option String) (render : RunReport → String) : IO Unit := do
    if let some path := path? then writeFile path (render report)
  write junit? junitReport
  write json? jsonReport
  write markdown? markdownReport

/--
Runs or lists the tests as {name}`execute` does, with the human-readable output on standard output,
colored when {name}`color` is true, and the events in the file that the options name; then writes
the report files of a run and prints the issues. The result is {name}`execute`'s exit code. A
cancelled run writes no report files and returns {name}`ExitCode.other`. With {name}`progress?`,
the human-readable lines go through the progress display, which is cleared however the run ends.
-/
def executeAndWrite (config : Config) (opts : Options)
    (registry : Option Registry := none) (color : Bool := false)
    (progress? : Option Progress.Display := none) : IO UInt32 := do
  let registry ← match registry with
    | some r => pure r
    | none => Registry.new
  let events? ← opts.eventsPath.mapM fun p => do
    if let some parent := (p : System.FilePath).parent then IO.FS.createDirAll parent
    IO.FS.Handle.mk p .append
  -- The dispatcher also prints from the threads that watch the tests, so every line goes to the
  -- standard output that the calling thread has here.
  let stdout ← IO.getStdout
  let sinks : Sinks := {
    event := fun j => do
      if let some h := events? then
        h.putStr (j.compress ++ "\n")
        h.flush
    line := match progress? with
      | some p => p.print
      | none => fun l => do
        stdout.putStrLn l
        stdout.flush
  }
  let (report, code) ← execute config opts sinks registry color progress?
  -- A cancelled run writes no reports.
  if ← registry.cancelled then return ExitCode.other
  if opts.command == .run then writeReports config opts report
  for issue in report.issues do
    IO.eprintln s!"{issue.level}: {issue.message}"
  return code

/--
Cancels the run once the runner's lifeline, its standard input, closes: every later start is
refused, and the running processes are terminated and, after the grace period, killed; then the
run loop tears down the fixtures whose setups were invoked. The driver holds the other end of that
pipe, which closes when the driver exits, however it exits. After the cancellation, the run loop has
the grace period, four pipe graces, two more seconds, and the time that each teardown it starts may
take to end, and then the runner exits with {lit}`1`. The progress display, when there is one, is
cleared before the runner prints anything about the cancellation.
-/
def exitWhenStdinCloses (parentIn : IO.FS.Stream) (registry : Registry) (graceMs : Nat)
    (progress? : Option Progress.Display := none) : IO Unit := do
  repeat
    if (← parentIn.getLine).isEmpty then break
  if let some p := progress? then
    try p.clear catch _ => pure ()
  try IO.eprintln "errata-runner: standard input closed, so the run ends" catch _ => pure ()
  registry.cancel graceMs
  -- The run loop reaps the processes, ends what they left holding their pipes, and runs the
  -- teardowns; this bounds how long that may take.
  let start ← IO.monoMsNow
  repeat
    let c ← registry.state.atomically get
    if c.done || (← IO.monoMsNow) ≥ start + graceMs + 4 * pipeGraceMs + 2000 + c.allowanceMs then
      break
    IO.sleep 50
  -- The run loop ends the process itself once it is done; this ends it when the bound passes.
  unless (← registry.state.atomically get).done do
    try (← IO.getStdout).flush catch _ => pure ()
    IO.Process.forceExit 1

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
The driver's planning mode, {lit}`errata-runner errata-plan REQUEST OUT ARGS...`, which the driver
runs before it builds any test executable. {name}`request` is a JSON object with the path of
{lit}`config.json` under {lit}`config`, the command that the arguments follow under
{lit}`invocation`, and the names of the test executables that the package can have under
{lit}`executables`. The mode reads the command line {name}`args` as a run would, checks the profile
and the filters, and writes to the file {name}`out` a JSON object with the command, the profile,
the executables that the filters do not rule out by their names alone, whether the targets that
the profile's settings need must be built, whether the phases are named as they begin, and the
modules that {lit}`--interpreted` names. When the command line asks for the usage text, the mode
prints it and writes {lit}`{"help": true}`. The result is the exit code: {name}`ExitCode.ok`, or the
code of the problem, which the mode reports.
-/
def plan (request out : String) (args : List String) : IO UInt32 := do
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
    try IO.ofExcept (Config.ofJson (← readJsonFile configPath) (Json.mkObj []) none)
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
      ("needs", Json.bool opts.resolvesSettings),
      ("phases", Json.bool (opts.command == .run && opts.verbosity.showsPasses)),
      ("interpreted", ToJson.toJson opts.interpreted)]
    return ExitCode.ok

/--
The runner's entry point: {lit}`errata-runner CONFIG WORKSPACE [run|list] [OPTIONS]
[NAME-FILTER]... [-- NAME-FILTER...]`, where {lit}`CONFIG` is the {lit}`config.json` that
{lit}`errata-config` writes and {lit}`WORKSPACE` the {lit}`workspace.json` that the driver writes;
or {lit}`errata-runner errata-plan …`, which {name}`plan` describes. The workspace's
{lit}`invocation`, when it has one, names the command in the usage text. When
{lit}`ERRATA_LIFELINE` is {lit}`1` in its environment, the runner watches its standard input and
cancels the run when it closes. The profile is {lit}`ERRATA_PROFILE` when the command line names
none.
-/
def main (args : List String) : IO UInt32 := do
  if let "errata-plan" :: request :: out :: rest := args then
    return ← plan request out rest
  let invocation ← do
    match args with
    | _ :: path :: _ =>
      if path.startsWith "-" then pure none
      else
        try pure ((← readJsonFile path).getObjValAs? String "invocation").toOption
        catch _ => pure none
    | _ => pure none
  let invocation := invocation.getD "errata-runner CONFIG WORKSPACE"
  let opts ← match parseOptions args (← IO.getEnv "ERRATA_PROFILE") with
    | .ok opts => pure opts
    | .error msg => return ← badCommandLine args invocation msg
  if opts.help then
    IO.print (usage invocation)
    return ExitCode.ok
  -- The targets that the profile's settings need are built for a run, and for a listing that shows
  -- what each test receives.
  let required? := if opts.resolvesSettings then some opts.profile else none
  let config ←
    try Config.load opts.configPath opts.workspacePath required?
    catch e =>
      IO.eprintln s!"error: {e}"
      return ExitCode.setupError
  let registry ← Registry.new
  let grace := opts.gracePeriodMs?.getD defaultGracePeriodMs
  let color ← useColor opts.color
  let progress? ←
    if ← Progress.enabled opts then some <$> Progress.Display.new (← IO.getStdout) color
    else pure none
  -- The driver sets the variable when it gives the runner a standard input to watch.
  if (← IO.getEnv lifelineVariable) == some "1" then
    let _ ← IO.asTask (prio := .dedicated)
      (exitWhenStdinCloses (← IO.getStdin) registry grace progress?)
  let code ← executeAndWrite config opts (some registry) color progress?
  registry.finish
  try (← IO.getStdout).flush catch _ => pure ()
  try (← IO.getStderr).flush catch _ => pure ()
  -- The thread that reads standard input runs until the pipe closes, and a Lean program that
  -- returns from `main` waits for its threads, so the runner ends the process itself.
  IO.Process.forceExit code.toUInt8
