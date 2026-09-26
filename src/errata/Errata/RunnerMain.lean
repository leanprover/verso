/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The runner's Run phase and its entry point: the `run` subcommand reads a plan and the values of the
needs it names, runs each selected test in a process of its own under a timeout, merges what the
test executable reported with what it observed from outside, and writes the reports.
-/
module

public import Errata.Planner
public import Errata.Scheduler
public import Errata.Progress
public import Std.Sync.Mutex
import all Errata.FS

public section

set_option linter.missingDocs true
set_option doc.verso true

open Lean (Json ToJson)

namespace Errata.Runner

open ProcessControl

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

/--
Ends the run: the dispatcher learns that it is over, and the result is the report with the exit code
{name}`code`. The human report prints its summary when {name}`summary` is true, with the counts of
{name}`skipped?`; {name}`order` is the order of the JUnit report.
-/
def Dispatcher.finishRun (d : Dispatcher) (runSeed : Nat) (runId : String) (summary : Bool)
    (code : UInt32) (skipped? : Option (Nat × Nat × Nat) := none)
    (order : Array Result.Key := #[]) : IO (RunReport × UInt32) := do
  d.dispatch (.ended (← Protocol.nowMs) summary skipped?)
  let s ← d.get
  return ({ results := s.results, issues := s.issues, seed := runSeed, runId, order }, code)

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

/-- The environment variables that every test executable of the run receives. -/
def RunContext.env (ctx : RunContext) (exe : ExecutableConfig) : Array (String × Option String) :=
  executableEnv ctx.config ctx.runId exe

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
structure Schedule where
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
The schedule of a run with {name}`pool` slots, the {name}`selected` tests, and the {name}`fixtures`
that they need, directly or through other fixtures, each after the fixtures it takes.
-/
def Schedule.of (pool : Nat) (selected : Array (InventoryTest × Resolved))
    (fixtures : Array (Nat × InventoryFixture × Resolved)) : Schedule := Id.run do
  let mut index : Std.HashMap (Nat × String) Nat := {}
  let mut specs : Array Scheduler.FixtureSpec := #[]
  for h : i in [0 : fixtures.size] do
    let (e, f, r) := fixtures[i]
    index := index.insert (e, f.name) i
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
def Schedule.settingConflicts (schedule : Schedule) : Array String := Id.run do
  let mut out := #[]
  for h : t in [0 : schedule.tests.size] do
    let (test, r) := schedule.tests[t]
    for f in Scheduler.closureOf schedule.fixtureSpecs
        (schedule.testSpecs[t]!.fixtures.map (·.1)) do
      let (_, fixture, fr) := schedule.fixtures[f]!
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
def Schedule.boundsRuntime (schedule : Schedule) : Bool := schedule.pool > 1

/-- The grant of a request of {name}`n` threads in the schedule's pool. -/
def Schedule.grant (schedule : Schedule) (n : Nat) : Nat := max 1 (min n schedule.pool)

/-- The thread grant of a test: its request, one when it asks for none, within the pool. -/
def Schedule.testThreads (schedule : Schedule) (t : Nat) : Nat :=
  schedule.grant (schedule.tests[t]!.1.threads?.getD 1)

/--
The thread grant of a fixture's phases: its request, one when it asks for none, within the pool.
-/
def Schedule.fixtureThreads (schedule : Schedule) (f : Nat) : Nat :=
  schedule.grant (schedule.fixtures[f]!.2.1.threads?.getD 1)

/-- Fixtures' values, given by the fixtures' positions, by the fixtures' names. -/
def Schedule.namedValues (schedule : Schedule) (values : Array (Nat × String)) :
    Array (String × String) :=
  values.map fun (i, v) => (schedule.fixtures[i]!.2.1.name, v)

/-- The arguments of one phase of a fixture, with the values of the given fixtures. -/
def Schedule.phaseArgs (schedule : Schedule) (out : String) (f : Nat) (phase : FixturePhase)
    (values : Array (Nat × String)) : Array String :=
  let (_, fixture, r) := schedule.fixtures[f]!
  fixtureArgs out fixture.name phase r.settings (schedule.namedValues values)
    (schedule.fixtureThreads f)

/-- The arguments of a test, with the values of the given fixtures. -/
def Schedule.testArgs (schedule : Schedule) (out : String) (t : Nat)
    (values : Array (Nat × String)) : Array String :=
  let (test, r) := schedule.tests[t]!
  runArgs out test.name r.arguments (schedule.namedValues values) (schedule.testThreads t)

/--
The command that reproduces a job by hand: the setups of the fixtures it needs, each after those it
takes, then the prepares and the test for a test, or the job itself for a fixture's phase, then the
teardowns, in the reverse order of the setups. The chain supplies the fixtures' values.
-/
def RunContext.reproduceJob (ctx : RunContext) (schedule : Schedule) (job : Scheduler.Job) :
    String :=
  let out := "/dev/stderr"
  let (exeIdx, roots, middle, threads) : Nat × Array Nat × Array (Array String) × Nat :=
    match job with
    | .test t =>
      let direct := schedule.testSpecs[t]!.fixtures.map (·.1)
      (schedule.tests[t]!.1.exeIdx, direct,
        direct.map (schedule.phaseArgs out · .prepare #[]) ++ #[schedule.testArgs out t #[]],
        schedule.testThreads t)
    | .setup f | .teardown f => (schedule.fixtures[f]!.1, #[f], #[], schedule.fixtureThreads f)
    | .prepare f _ =>
      (schedule.fixtures[f]!.1, #[f], #[schedule.phaseArgs out f .prepare #[]],
        schedule.fixtureThreads f)
  let closure := Scheduler.closureOf schedule.fixtureSpecs roots
  let links := closure.map (schedule.phaseArgs out · .setup #[]) ++ middle ++
    closure.reverse.map (schedule.phaseArgs out · .teardown #[])
  ctx.reproduceChain ctx.config.executables[exeIdx]! links
    (if schedule.boundsRuntime then some threads else none)

/-- What the dispatcher knows of a job before it runs. -/
def RunContext.plannedJob (ctx : RunContext) (schedule : Schedule) (job : Scheduler.Job) :
    Planned :=
  let reproduce := ctx.reproduceJob schedule job
  match job with
  | .test t =>
    let (test, r) := schedule.tests[t]!
    { ctx.planned ctx.config.executables[test.exeIdx]! test r with reproduce }
  | .setup f | .prepare f _ | .teardown f =>
    let (e, fixture, r) := schedule.fixtures[f]!
    let (key, path, phase, preparedTest?) := match job with
      | .prepare _ t =>
        let name := schedule.tests[t]!.1.name
        (s!"prepare {name}", #[fixture.name, "prepare", name], FixturePhase.prepare, some name)
      | .teardown _ => ("teardown", #[fixture.name, "teardown"], .teardown, none)
      | _ => ("setup", #[fixture.name, "setup"], .setup, none)
    { exe := ctx.config.executables[e]!.name, test := fixture.name, key, kind := .fixture, path
      phase? := some phase, preparedTest?
      description? := fixture.description?, settings := r.settings
      seed? := (r.settings.find? (·.1 == seedSetting)).map (·.2), reproduce
      slowAfterMs := r.slowAfterMs }

/-- The key of the results of a job: its test's, or its fixture's phase's. -/
def RunContext.jobKey (ctx : RunContext) (schedule : Schedule) (job : Scheduler.Job) :
    Result.Key :=
  match job with
  | .test t =>
    let test := schedule.tests[t]!.1
    { exe := ctx.config.executables[test.exeIdx]!.name, test := test.name }
  | .setup f | .prepare f _ | .teardown f =>
    let (e, fixture, _) := schedule.fixtures[f]!
    let phase := match job with
      | .prepare _ t => #[fixture.name, "prepare", schedule.tests[t]!.1.name]
      | .teardown _ => #[fixture.name, "teardown"]
      | _ => #[fixture.name, "setup"]
    { exe := ctx.config.executables[e]!.name, test := fixture.name, phase }

/--
The schedule with its tests in the order that {name}`positions` gives by their current positions.
-/
def Schedule.reorder (schedule : Schedule) (positions : Array Nat) : Schedule :=
  { schedule with
    tests := positions.map (schedule.tests[·]!)
    testSpecs := positions.map (schedule.testSpecs[·]!) }

/--
The key of each test's group in the scheduling order: the executables and names of the fixtures that
the test takes, directly or through other fixtures, or the test's own executable and name when it
takes none. Each test without fixtures is thus a group of its own.
-/
def RunContext.groupKeys (ctx : RunContext) (schedule : Schedule) : Array String :=
  (List.range schedule.tests.size).toArray.map fun t =>
    let closure :=
      Scheduler.closureOf schedule.fixtureSpecs (schedule.testSpecs[t]!.fixtures.map (·.1))
    if closure.isEmpty then
      let key := ctx.jobKey schedule (.test t)
      s!"test\x00{key.exe}\x00{key.test}"
    else
      "fixtures" ++ String.join (closure.toList.map fun f =>
        let (e, fixture, _) := schedule.fixtures[f]!
        s!"\x00{ctx.config.executables[e]!.name}\x00{fixture.name}")

/--
The fixtures among {name}`fs` in the order of their teardowns: each after every fixture among them
that takes it, and otherwise the earliest in the schedule first.
-/
def Schedule.teardownOrder (schedule : Schedule) (fs : Array Nat) : Array Nat := Id.run do
  let mut left := fs.qsort (· < ·)
  let mut out := #[]
  while !left.isEmpty do
    let ready? := left.find? fun f => !left.any fun g => schedule.fixtureSpecs[g]!.deps.contains f
    -- Fixtures come after the fixtures they take, so the latest one left is always ready.
    let f := ready?.getD left.back!
    out := out.push f
    left := left.filter (· != f)
  return out

/--
The keys of the tests and fixtures' phases of a schedule in the order of the JUnit report. The tests
stand in the schedule's order, each after the prepares of its fixtures, in the order it names them.
Fixtures' setups stand before the first test that needs the fixture, directly or through other
fixtures, each after the setups of the fixtures it takes. Their teardowns stand after the last such
test, each before the teardowns of the fixtures it takes. A schedule in the inventory's order gives
the inventory's order.
-/
def RunContext.reportOrder (ctx : RunContext) (schedule : Schedule) : Array Result.Key := Id.run do
  let closures := schedule.testSpecs.map fun spec =>
    Scheduler.closureOf schedule.fixtureSpecs (spec.fixtures.map (·.1))
  let mut firstUser : Std.HashMap Nat Nat := {}
  let mut lastUser : Std.HashMap Nat Nat := {}
  for h : t in [0 : closures.size] do
    for f in closures[t] do
      firstUser := firstUser.insertIfNew f t
      lastUser := lastUser.insert f t
  let mut out := #[]
  for h : t in [0 : closures.size] do
    for f in closures[t] do
      if firstUser.get? f == some t then out := out.push (ctx.jobKey schedule (.setup f))
    for (f, _) in schedule.testSpecs[t]!.fixtures do
      out := out.push (ctx.jobKey schedule (.prepare f t))
    out := out.push (ctx.jobKey schedule (.test t))
    let ending := closures[t].filter (lastUser.get? · == some t)
    for f in schedule.teardownOrder ending do
      out := out.push (ctx.jobKey schedule (.teardown f))
  return out

/-- The invocation that runs a job, with the values of the fixtures it receives. -/
def RunContext.invocation (ctx : RunContext) (schedule : Schedule) (job : Scheduler.Job)
    (values : Array (Nat × String)) : Invocation :=
  let planned := ctx.plannedJob schedule job
  match job with
  | .test t =>
    let (test, r) := schedule.tests[t]!
    { exe := ctx.config.executables[test.exeIdx]!, planned
      args := (schedule.testArgs · t values), threads := schedule.testThreads t
      boundRuntime := schedule.boundsRuntime
      timeoutMs := r.timeoutMs, gracePeriodMs := r.gracePeriodMs }
  | .setup f | .prepare f _ | .teardown f =>
    let (e, _, r) := schedule.fixtures[f]!
    let phase : FixturePhase := match job with
      | .prepare .. => .prepare
      | .teardown _ => .teardown
      | _ => .setup
    { exe := ctx.config.executables[e]!, planned
      args := (schedule.phaseArgs · f phase values), threads := schedule.fixtureThreads f
      boundRuntime := schedule.boundsRuntime
      timeoutMs := r.timeoutMs, gracePeriodMs := r.gracePeriodMs }

/--
Runs the schedule's tests and the phases of their fixtures, as the scheduler directs: it starts each
job that the scheduler asks for, reports the tests and setups that it asks to report without
running, and tells it of each process that ends, until it ends the run. Once the run has been
cancelled, the scheduler learns of it before the next command, starts no more tests, and tears down
the fixtures whose setups were invoked. When nothing runs and the scheduler has not ended the run,
the tests it never started are named in a run-level error.
-/
def RunContext.runScheduled (ctx : RunContext) (schedule : Schedule) : IO Unit := do
  let d := ctx.dispatcher
  let mut sched := Scheduler.State.init schedule.pool schedule.testSpecs schedule.fixtureSpecs
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
        let p := ctx.plannedJob schedule job
        let exit : Exit := match reason with
          | .settingMissing s => .settingMissing s
          | .fixtureFailed f phase => .fixtureFailed schedule.fixtures[f]!.2.1.name phase
        d.dispatch (.testStarted p)
        d.dispatch (.testEnded p.exe p.test p.key exit 0)
      | .spawn job _ values =>
        let teardown := job matches .teardown _
        match ← ctx.launch (ctx.invocation schedule job values) launched teardown with
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
        let pending := (List.range schedule.tests.size).filter fun t =>
          !(sched.testStatus[t]! matches .done)
        let names := pending.map (schedule.tests[·]!.1.name)
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

/--
The message of a run that selects no test under {lit}`--no-tests fail`.
-/
def noTestsMessage : String :=
  "no tests to run; --no-tests warn or --no-tests pass accepts a run that selects none"

/--
The Run phase of the plan: its selected tests and the phases of the fixtures they use run as the
scheduler directs, in the scheduling order as far as the fixtures' claims and the slots of the pool
allow. What each receives is the plan's, with each need's value from {name}`needValues` and each
derived seed drawn from {name}`runSeed`. The scheduling order is the inventory's, or under the
profile's {lit}`order = "shuffle"` the order that {name}`Scheduler.groupedOrder` draws from the
run's seed, in which tests that take the same fixtures stand together. The pool has the slots that
{lit}`--jobs` or else the profile's {lit}`jobs` gives, or else one per CPU available to the runner.
When {name}`progress?` gives a progress display, the phase starts it as it begins. The result is the
exit code, the counts that the summary reports as skipped, and the order of the JUnit report, which
lists the tests in the inventory's order whatever the scheduling order.
-/
def runPhase (d : Dispatcher) (registry : Registry) (lifelines : Lifelines) (plan : Plan)
    (needValues : Array (String × String)) (opts : Options) (runSeed : Nat) (runId : String)
    (progress? : Option Progress.Display := none) :
    IO (UInt32 × (Nat × Nat × Nat) × Array Result.Key) := do
  let config := plan.config
  let profile := (config.profile? plan.profile).getD { name := plan.profile }
  let selected := plan.tests.map fun t =>
    (t.test, t.resolution.substitute needValues runSeed (plan.exeName t.test.exeIdx) t.test.name)
  let fixtures := plan.fixtures.map fun f =>
    (f.exeIdx, f.fixture,
      f.resolution.substitute needValues runSeed (plan.exeName f.exeIdx) f.fixture.name)
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
  let exeWidth := selected.foldl (init := 0) fun w (t, _) => max w (plan.exeName t.exeIdx).length
  d.state.atomically (modify fun s => { s with human := { s.human with exeWidth } })
  d.dispatch (.phase "Run" (← Protocol.nowMs) (some pool))
  let inventorySchedule := Schedule.of pool selected fixtures
  for w in inventorySchedule.settingConflicts do
    d.dispatch (.issue { isError := false, message := w })
  IO.FS.withTempDir fun dir => do
    let ctx : RunContext :=
      { config, opts, runSeed, runId, dir, dispatcher := d, registry, lifelines }
    let schedule := match profile.order?.getD .default with
      | .default => inventorySchedule
      | .shuffle =>
        inventorySchedule.reorder
          (Scheduler.groupedOrder runSeed (ctx.groupKeys inventorySchedule))
    if let some p := progress? then p.start schedule.tests.size exeWidth
    ctx.runScheduled schedule
    let s ← d.get
    -- Under `--wfail`, the warning of `--no-tests warn` fails the run as `--no-tests fail` does.
    let code :=
      if selected.isEmpty && (opts.noTests == .fail || (opts.noTests == .warn && opts.wfail)) then
        ExitCode.noTestsRun
      else if s.results.all (·.outcome.isPass) && !s.issues.any (·.isError) then ExitCode.ok
      else ExitCode.testRunFailed
    return (code, (plan.skipped, config.skippedTestLibraries.size,
      config.skippedExecutables.size), ctx.reportOrder inventorySchedule)

/--
A dispatcher for a run with the options {name}`opts`. The human report of a listing, which
{name}`listing` marks, prints nothing of its own.
-/
def newDispatcher (opts : Options) (sinks : Sinks) (color : Bool) (runSeed : Nat) (listing : Bool)
    (progress? : Option Progress.Display) : IO Dispatcher := do
  -- A listing prints no results, so its reporter prints nothing of its own.
  let human : HumanReporter := { verbosity := if listing then .silent else opts.verbosity, color }
  return {
    state := ← Std.Mutex.new {
      human, wfail := opts.wfail, startMs := ← Protocol.nowMs, seed? := some runSeed }
    sinks, progress? }

/-- The events file's first record: its version, the run's identifier, and the run's seed. -/
def protocolRecord (runId : String) (runSeed : Nat) : Json :=
  Json.mkObj [("type", Json.str "protocol"), ("version", ToJson.toJson Protocol.version),
    ("run_id", Json.str runId), ("seed", ToJson.toJson runSeed)]

/--
Plans and then runs or lists the tests of every test executable in the configuration in one process,
reporting to {name}`sinks` as the run proceeds, and returns the report with the exit code. The
events file's lines and the human-readable report's lines go to the sinks; the report files are the
caller's to write. The {lit}`protocol` line of the events file is sent first. The human-readable
report is colored when {name}`color` is true.

{name}`makePlan` plans the run, and its issues reach the dispatcher as it finds them; a problem that
ends the planning ends the run with its exit code. The {lit}`list` command then prints the selected
tests in its message format, and a run goes on with {name}`runPhase`, with {name}`needValues` as the
needs' values. However the run ends, it closes the held lifelines and clears the progress display.
-/
def execute (config : Config) (opts : Options) (sinks : Sinks)
    (registry : Option Registry := none) (color : Bool := false)
    (progress? : Option Progress.Display := none) (needValues : Array (String × String) := #[]) :
    IO (RunReport × UInt32) := do
  let runSeed ← match opts.seed with
    | some s => pure s
    | none => IO.rand 0 (2 ^ 32 - 1)
  let runId ← newRunId
  let listing := opts.command == .list
  let d ← newDispatcher opts sinks color runSeed listing progress?
  sinks.event (protocolRecord runId runSeed)
  let registry ← match registry with
    | some r => pure r
    | none => Registry.new
  let lifelines ← Lifelines.new
  -- However the run ends, the held lifelines close and the progress display is cleared.
  let closeRun : IO Unit := do
    lifelines.closeAll
    if let some p := progress? then p.clear
  flip tryFinally closeRun do
    let planned ← makePlan config opts registry runId (report := fun i => d.dispatch (.issue i))
      (onList := do d.dispatch (.phase "List" (← Protocol.nowMs) none))
    match planned with
    | .error code => d.finishRun runSeed runId (!listing) code
    | .ok plan =>
      if listing then
        printPlan plan opts sinks.line color runSeed
        d.finishRun runSeed runId false ExitCode.ok
      else
        let (code, skipped, order) ←
          runPhase d registry lifelines plan needValues opts runSeed runId progress?
        d.finishRun runSeed runId true code skipped order

/--
Runs the plan's tests, reporting to {name}`sinks` as the run proceeds, and returns the report with
the exit code. The run's seed is the plan's when the command line gave it one, and otherwise drawn
now. The events file begins with the {lit}`protocol` record and the {lit}`phase` record of the List
phase, stamped as the run reads the plan, and the plan's issues follow; then {name}`runPhase` runs
the tests with {name}`needValues` as the needs' values. However the run ends, it closes the held
lifelines and clears the progress display.
-/
def executePlan (plan : Plan) (needValues : Array (String × String)) (opts : Options)
    (sinks : Sinks) (registry : Option Registry := none) (color : Bool := false)
    (progress? : Option Progress.Display := none) : IO (RunReport × UInt32) := do
  let runSeed ← match plan.seed? <|> opts.seed with
    | some s => pure s
    | none => IO.rand 0 (2 ^ 32 - 1)
  let runId ← newRunId
  let d ← newDispatcher opts sinks color runSeed false progress?
  sinks.event (protocolRecord runId runSeed)
  let registry ← match registry with
    | some r => pure r
    | none => Registry.new
  let lifelines ← Lifelines.new
  let closeRun : IO Unit := do
    lifelines.closeAll
    if let some p := progress? then p.clear
  flip tryFinally closeRun do
    d.dispatch (.phase "List" (← Protocol.nowMs) none)
    for issue in plan.issues do d.dispatch (.issue issue)
    let (code, skipped, order) ←
      runPhase d registry lifelines plan needValues opts runSeed runId progress?
    d.finishRun runSeed runId true code skipped order

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
The sinks of a run of this process: the human-readable lines on standard output, or through the
progress display when there is one, and the events appended to the file that the options name.
-/
def processSinks (opts : Options) (progress? : Option Progress.Display) : IO Sinks := do
  let events? ← opts.eventsPath.mapM fun p => do
    if let some parent := (p : System.FilePath).parent then IO.FS.createDirAll parent
    IO.FS.Handle.mk p .append
  -- The dispatcher also prints from the threads that watch the tests, so every line goes to the
  -- standard output that the calling thread has here.
  let stdout ← IO.getStdout
  return {
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

/--
Writes the report files of a run of the configuration {name}`config`, unless the run was cancelled
or listed, and prints the issues. The result is the run's exit code {name}`code`, or
{name}`ExitCode.other` for a cancelled run.
-/
def reportRun (config : Config) (opts : Options) (registry : Registry) (report : RunReport)
    (code : UInt32) : IO UInt32 := do
  -- A cancelled run writes no reports.
  if ← registry.cancelled then return ExitCode.other
  if opts.command == .run then writeReports config opts report
  for issue in report.issues do
    IO.eprintln s!"{issue.level}: {issue.message}"
  return code

/--
Runs or lists the tests as {name}`execute` does, with the human-readable output on standard output,
colored when {name}`color` is true, and the events in the file that the options name; then writes
the report files of a run and prints the issues. The result is {name}`execute`'s exit code. A
cancelled run writes no report files and returns {name}`ExitCode.other`. With {name}`progress?`,
the human-readable lines go through the progress display, which is cleared however the run ends.
-/
def executeAndWrite (config : Config) (opts : Options)
    (registry : Option Registry := none) (color : Bool := false)
    (progress? : Option Progress.Display := none)
    (needValues : Array (String × String) := #[]) : IO UInt32 := do
  let registry ← match registry with
    | some r => pure r
    | none => Registry.new
  let sinks ← processSinks opts progress?
  let (report, code) ← execute config opts sinks registry color progress? needValues
  reportRun config opts registry report code

/--
Runs the plan's tests as {name}`executePlan` does, with the output of {name}`executeAndWrite`, and
writes the report files and prints the issues as it does.
-/
def executePlanAndWrite (plan : Plan) (needValues : Array (String × String)) (opts : Options)
    (registry : Registry) (color : Bool := false)
    (progress? : Option Progress.Display := none) : IO UInt32 := do
  let sinks ← processSinks opts progress?
  let (report, code) ← executePlan plan needValues opts sinks registry color progress?
  reportRun plan.config { opts with profile := plan.profile } registry report code

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
Reads the values of the needs from {lit}`workspace.json`: an object whose {lit}`needs` maps each
need's name to its value.
-/
def readNeedValues (path : System.FilePath) : IO (Array (String × String)) := do
  let j ← readJsonFile path
  match j.getObjVal? "needs" with
  | .ok .null | .error _ => return #[]
  | .ok n =>
    let obj ← IO.ofExcept (n.getObj? |>.mapError (s!"{path}: needs: " ++ ·))
    obj.toArray.mapM fun (k, v) => do
      return (k, ← IO.ofExcept (v.getStr? |>.mapError (s!"{path}: needs.{k}: " ++ ·)))

/--
The {lit}`run` subcommand, {lit}`errata-runner run PLAN WORKSPACE [run] [OPTIONS]`, where
{lit}`PLAN` is the plan that the {lit}`plan` subcommand wrote and {lit}`WORKSPACE` the
{lit}`workspace.json` in which the driver gives the value of each need that the plan names. It runs
the plan's tests with the options that the command line gives the Run phase and writes the reports.
Every need of the plan must have a value. When {lit}`ERRATA_LIFELINE` is {lit}`1` in its
environment, the runner watches its standard input and cancels the run when it closes.
-/
def runMain (args : List String) : IO UInt32 := do
  let invocation ← do
    match args with
    | path :: _ =>
      if path.startsWith "-" then pure none
      else
        try pure (← Plan.load path).config.invocation?
        catch _ => pure none
    | _ => pure none
  let invocation := invocation.getD "errata-runner run PLAN WORKSPACE"
  let opts ← match parseOptions args (← IO.getEnv "ERRATA_PROFILE") with
    | .ok opts => pure opts
    | .error msg => return ← badCommandLine args invocation msg
  if opts.help then
    IO.print (usage invocation)
    return ExitCode.ok
  let loaded ← try
      let plan ← Plan.load opts.planPath
      let needValues ← readNeedValues opts.workspacePath
      pure (Except.ok (plan, needValues))
    catch e => pure (.error (toString e))
  let (plan, needValues) ← match loaded with
    | .ok p => pure p
    | .error e =>
      IO.eprintln s!"error: {e}"
      return ExitCode.setupError
  let absent := plan.needs.filter fun n => !needValues.any (·.1 == n.need.name)
  unless absent.isEmpty do
    for n in absent do
      IO.eprintln s!"error: {opts.workspacePath} gives no value for the need {n.need.name}"
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
  let code ← executePlanAndWrite plan needValues opts registry color progress?
  registry.finish
  try (← IO.getStdout).flush catch _ => pure ()
  try (← IO.getStderr).flush catch _ => pure ()
  -- The thread that reads standard input runs until the pipe closes, and a Lean program that
  -- returns from `main` waits for its threads, so the runner ends the process itself.
  IO.Process.forceExit code.toUInt8

/-- The runner's subcommands and their arguments, for the message of an unknown command line. -/
def subcommandsText : String :=
  "\n".intercalate [
    "usage: errata-runner check REQUEST OUT [ARGS...]",
    "       errata-runner plan CONFIG EXECUTABLES OUT [ARGS...]",
    "       errata-runner list PLAN [ARGS...]",
    "       errata-runner run PLAN WORKSPACE [ARGS...]"]

/--
The runner's entry point, whose first argument names the subcommand: {lit}`check`, which
{name}`checkMain` describes, {lit}`plan`, which {name}`planMain` describes, {lit}`list`, which
{name}`listMain` describes, or {lit}`run`, which {name}`runMain` describes. The profile is
{lit}`ERRATA_PROFILE` when the command line names none.
-/
def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: request :: out :: rest => checkMain request out rest
  | "plan" :: config :: executables :: out :: rest => planMain config executables out rest
  | "list" :: plan :: rest => listMain plan rest
  | "run" :: rest => runMain rest
  | _ =>
    IO.eprintln subcommandsText
    return ExitCode.usage

end Errata.Runner
