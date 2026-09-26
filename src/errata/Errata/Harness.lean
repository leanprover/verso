/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The Lean harness: the main of a library's test executable. It lists the library's tests and the
fixtures they use, runs one test or one phase of a fixture by name and writes the protocol's records
to the file the runner names, and runs the helpers that its tests start.
-/
module

public import Errata.Runner
public import Errata.Helpers
public import Errata.Protocol
public import Errata.ProcessControl
public import Std.Data.HashMap

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata.Harness

open Protocol

/-- The usage message of a test executable. -/
def usage : String :=
  "usage:\n  \
    <test-executable> errata-list <out>\n  \
    <test-executable> errata-run <out> <test-name> [setting:NAME=VALUE]... [fixture:NAME=VALUE]... \
      [threads:N]\n  \
    <test-executable> errata-fixture <out> <fixture-name> setup|prepare|teardown \
      [setting:NAME=VALUE]... [fixture:NAME=VALUE]... [threads:N]\n  \
    <test-executable> errata-helper <helper-name> [ARG]...\n\n\
    Several errata-list, errata-run, and errata-fixture invocations may be chained, each \
    separated by a ';' argument. The Errata runner starts test executables, and tests start their \
    helpers. To run the tests, run the Errata driver, which is usually `lake test`."

/--
The arguments of the given kind among a test executable's arguments: each {lit}`KIND:NAME=VALUE`,
split at the first {lit}`=`, in order. Arguments of any other form are ignored.
-/
def pairsOf (kind : String) (args : List String) : Array (String × String) :=
  args.toArray.filterMap fun arg => do
    let rest ← arg.dropPrefix? s!"{kind}:"
    match rest.copy.splitOn "=" with
    | [] => none
    | [name] => some (name, "")
    | name :: value => some (name, "=".intercalate value)

/--
The settings among a test executable's arguments: each {lit}`setting:NAME=VALUE`, split at the first
{lit}`=`, in order. Arguments of any other form are ignored.
-/
def settingsOf (args : List String) : Array (String × String) :=
  pairsOf "setting" args

/--
The fixtures' values among a test executable's arguments: each {lit}`fixture:NAME=VALUE`, split at
the first {lit}`=`, in order. Arguments of any other form are ignored.
-/
def fixturesOf (args : List String) : Array (String × String) :=
  pairsOf "fixture" args

/--
The thread grant among a test executable's arguments: the number in the last {lit}`threads:N` when
it is positive, and {lit}`1` otherwise.
-/
def threadsOf (args : List String) : Nat :=
  let grants := args.filterMap fun arg => (arg.dropPrefix? "threads:").bind (·.toNat?)
  (grants.getLast?.filter (· > 0)).getD 1

/--
The name of the setting that the Lean harness reads itself, whether or not a test takes it:
{name}`Errata.updateGolden`, which rewrites golden files when it is {lit}`true`. The runner passes
it for {lit}`--update-golden`.
-/
def updateGoldenName : String := settingNameOf ``Errata.updateGolden

/--
The module name that {name}`text` writes, read as Lean writes names, with {lit}`«»` around each
component that needs them.
-/
def moduleNameOf (text : String) : Lean.Name :=
  (Lean.Syntax.decodeNameLit ("`" ++ text)).getD text.toName

/--
The command that starts this test executable: {name}`invocation` when it is non-empty, and otherwise
the path of the running program.
-/
def selfCommand (invocation : Array String) : IO (Array String) := do
  if invocation.isEmpty then return #[(← IO.appPath).toString] else return invocation

/--
The context for a test run with the given settings and the thread grant {name}`threads`. The
harness's own setting configures it. Tests reach their helpers through this test executable's
{lit}`errata-helper` mode, which {name}`invocation` starts as {name}`selfCommand` describes.
-/
def contextOf (settings : Array (String × String)) (threads : Nat := 1)
    (invocation : Array String := #[]) : IO TestContext := do
  let lookup (name : String) : Option String := (settings.findRev? (·.1 == name)).map (·.2)
  let golden := lookup updateGoldenName >>= Errata.updateGolden.fromString
  let ctx ← mkContext (updateGolden := golden.getD false)
  return { ctx with
    helperCommand := some ((← selfCommand invocation).push "errata-helper"), threads }

/--
Adds the fixture named {name}`name`, looked up in {name}`byName`, to {name}`order` after the
fixtures it takes, each once. {name}`order` holds the fixtures added so far and the set of their
names.
-/
-- Each fixture is marked seen before the fixtures it takes are added, so each is visited once.
partial def addFixtureAfterItsFixtures (byName : Std.HashMap String FixtureInfo) (name : String)
    (order : Array FixtureInfo × Std.HashSet String) : Array FixtureInfo × Std.HashSet String :=
  let (out, seen) := order
  if seen.contains name then order
  else match byName.get? name with
    | none => order
    | some f =>
      let (out, seen) := f.fixtures.foldl (init := (out, seen.insert name)) fun acc d =>
        addFixtureAfterItsFixtures byName d acc
      (out.push f, seen)

/--
The fixtures among {name}`fixtures` that the tests in {name}`entries` use, directly or through the
fixtures they use, in the order in which the tests first reach them, each after the fixtures it
takes. The order depends on the tests alone, whatever the order of {name}`fixtures`.
-/
def reachedFixtures (entries : Array TestInfo) (fixtures : Array FixtureInfo) :
    Array FixtureInfo :=
  let byName : Std.HashMap String FixtureInfo := fixtures.foldl (init := {}) fun m f =>
    m.insert f.name f
  entries.foldl (init := (#[], {})) (fun acc e =>
    e.fixtures.foldl (init := acc) fun acc f => addFixtureAfterItsFixtures byName f.name acc) |>.1

/--
The settings that the tests in {name}`entries` and the fixtures in {name}`fixtures` take, each once,
in the order in which the entries, and then the fixtures, first name them.
-/
def reachedSettings (entries : Array TestInfo) (fixtures : Array FixtureInfo := #[]) :
    Array SettingRef := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut out := #[]
  for s in entries.flatMap (·.settings) ++ fixtures.flatMap (·.settings) do
    unless seen.contains s.name do
      seen := seen.insert s.name
      out := out.push s
  return out

/-- The names of the settings that a test or fixture record lists, or none for an empty list. -/
private def settingDeps (settings : Array SettingRef) : Option (Array String) :=
  if settings.isEmpty then none else some (settings.map (·.name))

/--
Writes the inventory: the protocol record; a setting record for each setting that the tests and
their fixtures take, with its description and its declared default; a fixture record for each
fixture that the tests use, directly or through other fixtures, in the order of
{name}`reachedFixtures`, with its description, the settings and fixtures it takes, and the threads
it asks for; and then a test record for each entry, with its tags and the settings and fixtures it
takes.
-/
def writeInventory (entries : Array TestInfo) (out : IO.FS.Handle)
    (fixtures : Array FixtureInfo := #[]) : IO Unit := do
  writeRecord out (.protocol (some version))
  let reached := reachedFixtures entries fixtures
  for s in reachedSettings entries reached do
    writeRecord out (.setting (some s.name) s.description? s.default?)
  for f in reached do
    writeRecord out <| .fixture {
      name? := some f.name, description? := f.docstring?, settings? := settingDeps f.settings
      fixtures? := if f.fixtures.isEmpty then none else some f.fixtures, threads? := f.threads?
    }
  for e in entries do
    writeRecord out <| .test {
      name? := some e.name, path? := some e.path, file? := some e.location.file
      line? := some e.location.startPos.line, col? := some e.location.startPos.column
      description? := e.docstring?
      tags? := if e.tags.isEmpty then none else some e.tags
      settings? := settingDeps e.settings
      fixtures? := if e.fixtures.isEmpty then none
        else some (e.fixtures.map fun f => { name := f.name, exclusive := f.exclusive })
      threads? := e.threads?
    }

/-- The record fields for the status of a finished check. -/
private def statusInfo : Errata.Status → Protocol.Status × Option String × Option String × Option Span
  | .pass => (.pass, none, none, none)
  | .fail f => (.fail, some f.message, f.detail?, f.location?.map Span.ofLocation)
  | .error m => (.error, some m, none, none)

/--
Runs one test, writing its records to {name}`out`: {lit}`start` as its body begins, an
{lit}`output` record for each fragment it writes, a {lit}`result` record as each named result starts
and again as it finishes, and a {lit}`verdict` at the end. Each output record names the named result
that was open when the fragment was written, {lit}`0` for the test itself. A named result that failed
within an {name (scope := "Errata.TestM")}`expectFail` that expected it is reported again with the
status {lit}`expectedFailure`. The test receives {name}`settings` and the fixtures' values
{name}`fixtures`. The result is the exit code: {lit}`0` for a pass and {lit}`1` otherwise.
-/
def runTest (entry : TestEntry) (ctx : TestContext) (settings : Array (String × String))
    (out : IO.FS.Handle) (fixtures : Array (String × String) := #[]) : IO UInt32 := do
  writeRecord out (.start (some (← nowMs)))
  -- The results that are open, innermost last, and the identifier of the next one. Output and
  -- result events arrive in the order the test produced them, so the result that wrote a fragment
  -- is the innermost one open when it arrives.
  let openResults ← IO.mkRef #[0]
  let nextResult ← IO.mkRef 1
  let innermost : IO Nat := return (← openResults.get).back?.getD 0
  -- For each `expectFail` whose action is running, innermost last, the reports of the named results
  -- that failed within it so far.
  let expecting ← IO.mkRef (#[] : Array (Array ResultInfo))
  let report (info : ResultInfo) : IO Unit := writeRecord out (.result info)
  let saveOutput (o : Output) : IO Unit := do
    let (stream, text) := match o with
      | .stdout s => ("stdout", s)
      | .stderr s => ("stderr", s)
    writeRecord out (.output (some stream) (some text) (some (← nowMs)) (some (← innermost)))
  let watch (ev : ResultEvent) : IO Unit := do
    match ev with
    | .started path =>
      let parent ← innermost
      let id ← nextResult.modifyGet fun n => (n, n + 1)
      openResults.modify (·.push id)
      report { id? := some id, parent? := some parent, name? := path.back? }
    | .finished r =>
      let id ← innermost
      openResults.modify (·.pop)
      let (status, message?, detail?, location?) := statusInfo r.status
      let info : ResultInfo := {
        id? := some id, parent? := some (← innermost), name? := r.resultPath.back?
        status? := some status, message?, detail?, location?, durationMs? := some r.durationMs
      }
      if status == .fail then
        expecting.modify fun frames =>
          if frames.isEmpty then frames else frames.modify (frames.size - 1) (·.push info)
      report info
    | .expectFailStarted => expecting.modify (·.push #[])
    | .expectFailFinished failuresExpected =>
      let failed ← expecting.modifyGet fun frames => (frames.back?.getD #[], frames.pop)
      if failuresExpected then
        for info in failed do
          report { info with status? := some .expectedFailure }
      else
        -- An error escaped the action, so its failures stay in the test's results, where an
        -- enclosing `expectFail` can still expect them.
        expecting.modify fun frames =>
          if frames.isEmpty then frames else frames.modify (frames.size - 1) (· ++ failed)
  let ctx := { ctx with writeOutput := some saveOutput, watchResults := some watch }
  let start ← IO.monoMsNow
  let results ← runEntry ctx entry settings fixtures
  let durationMs := (← IO.monoMsNow) - start
  let status := (results[0]?.map (·.status)).getD .pass
  let (st, message?, detail?, location?) := statusInfo status
  writeRecord out <|
    .verdict { status? := some st, message?, detail?, location?, durationMs? := some durationMs }
  return if status.isSuccess then 0 else 1

/--
Runs one phase of a fixture, writing its records to {name}`out`: an {lit}`output` record for each
fragment the phase writes, a {lit}`value` record with the value that a setup produced, and a
{lit}`verdict` when the phase failed. The phase receives {name}`settings`, the fixtures' values
{name}`fixtures`, among them its own value when the setup produced one, and the thread grant
{name}`threads`, and reaches its helpers through {name}`invocation`, as {name}`contextOf`
describes. The result is the exit code, {lit}`0` when the phase succeeded and {lit}`1` otherwise,
with the value that a setup produced.
-/
def runFixture (entry : FixtureEntry) (phase : FixturePhase) (settings : Array (String × String))
    (fixtures : Array (String × String)) (threads : Nat) (out : IO.FS.Handle)
    (invocation : Array String := #[]) : IO (UInt32 × Option String) := do
  let saveOutput (o : Output) : IO Unit := do
    let (stream, text) := match o with
      | .stdout s => ("stdout", s)
      | .stderr s => ("stderr", s)
    writeRecord out (.output (some stream) (some text) (some (← nowMs)) (some 0))
  let ctx : FixtureContext := {
    location := entry.location, description? := entry.docstring?, threads
    helperCommand := some ((← selfCommand invocation).push "errata-helper")
    writeOutput := some saveOutput, outputFailed := ← IO.mkRef false
    fixture := entry.name, phase
  }
  let own? := (fixtures.findRev? (·.1 == entry.name)).map (·.2)
  let start ← IO.monoMsNow
  let (outcome, _) ← runCapturing ctx (entry.run settings fixtures phase own?)
  let durationMs? := some ((← IO.monoMsNow) - start)
  match outcome with
  | .ok (.ok value?) =>
    if phase == .setup then
      let value := value?.getD ""
      writeRecord out (.value (some value))
      return (0, some value)
    return (0, none)
  | .ok (.error f) =>
    writeRecord out <| .verdict {
      status? := some .fail, message? := some f.message, detail? := f.detail?
      location? := f.location?.map Span.ofLocation, durationMs? }
    return (1, none)
  | .error e =>
    writeRecord out <|
      .verdict { status? := some .error, message? := some (toString e), durationMs? }
    return (1, none)

/-- The position of each entry, by its name. -/
def indexByName (entries : Array TestEntry) : Std.HashMap String Nat := Id.run do
  let mut index := {}
  for h : i in [0 : entries.size] do
    index := index.insert entries[i].name i
  return index

/-- The helpers, indexed by name. -/
def helpersByName (helpers : Array Helper) : Std.HashMap String Helper :=
  helpers.foldl (init := {}) fun m h => m.insert h.name h

/--
Runs the helper named {name}`name` from {name}`helpers` with {name}`args`, with the process's own
standard streams, and returns its exit code. For an unknown name, it writes a message to standard
error and returns {lit}`2`.
-/
def runHelperNamed (helpers : Array Helper) (name : String) (args : List String) : IO UInt32 := do
  match (helpersByName helpers).get? name with
  | some helper => helper.run args
  | none =>
    IO.eprintln s!"no helper is named {name}"
    return 2

/--
Performs one invocation of a test executable, and returns its exit code with the fixture and the
value that a setup produced. {lit}`errata-list` writes the inventory; {lit}`errata-run` runs the
named test, with the settings, fixtures' values, and thread grant that follow its name;
{lit}`errata-fixture` runs a phase of the named fixture from {name}`fixtures` likewise;
{lit}`errata-helper` runs the named helper from {name}`helpers` with the arguments that follow its
name; anything else prints the usage message. Tests and fixture phases reach their helpers through
{name}`invocation`, as {name}`contextOf` describes.
-/
def invoke (entries : Array TestEntry) (args : List String) (helpers : Array Helper := #[])
    (invocation : Array String := #[]) (fixtures : Array FixtureEntry := #[]) :
    IO (UInt32 × Option (String × String)) := do
  match args with
  | "errata-helper" :: name :: rest => return (← runHelperNamed helpers name rest, none)
  | ["errata-list", outPath] =>
    let out ← IO.FS.Handle.mk outPath .append
    writeInventory (entries.map (·.toTestInfo)) out (fixtures.map (·.toFixtureInfo))
    return (0, none)
  | "errata-run" :: outPath :: name :: rest =>
    let out ← IO.FS.Handle.mk outPath .append
    writeRecord out (.protocol (some version))
    let some entry := (indexByName entries).get? name |>.bind (entries[·]?)
      | writeRecord out (.verdict { status? := some .error, message? := some s!"no test is named {name}" })
        return (1, none)
    let settings := settingsOf rest
    let ctx ← contextOf settings (threadsOf rest) invocation
    return (← runTest entry ctx settings out (fixturesOf rest), none)
  | "errata-fixture" :: outPath :: name :: phaseName :: rest =>
    let some phase := FixturePhase.ofName? phaseName
      | IO.eprintln usage
        return (2, none)
    let out ← IO.FS.Handle.mk outPath .append
    writeRecord out (.protocol (some version))
    let some entry := fixtures.find? (·.name == name)
      | IO.eprintln s!"no fixture is named {name}"
        writeRecord out <|
          .verdict { status? := some .error, message? := some s!"no fixture is named {name}" }
        return (1, none)
    let (code, value?) ←
      runFixture entry phase (settingsOf rest) (fixturesOf rest) (threadsOf rest) out invocation
    return (code, value?.map (name, ·))
  | _ =>
    IO.eprintln usage
    return (2, none)

/--
Performs one invocation of a test executable, as {name}`invoke` does, and returns its exit code.
-/
def dispatch (entries : Array TestEntry) (args : List String) (helpers : Array Helper := #[])
    (invocation : Array String := #[]) (fixtures : Array FixtureEntry := #[]) : IO UInt32 :=
  return (← invoke entries args helpers invocation fixtures).1

/-- The invocations of a chain: the arguments, split at each {lit}`;` argument. -/
def chainLinks (args : List String) : List (List String) :=
  let (last, done) := args.foldl (init := ([], [])) fun (cur, done) a =>
    if a == ";" then ([], done ++ [cur]) else (cur ++ [a], done)
  done ++ [last]

/-- Whether an invocation runs a fixture's teardown. -/
def isTeardown (link : List String) : Bool :=
  link matches "errata-fixture" :: _ :: _ :: "teardown" :: _

/--
Performs the invocations of a chain in order with {name}`invoke`. Each value that a setup produces
is added to the later {lit}`errata-run` and {lit}`errata-fixture` invocations as that fixture's
{lit}`fixture:NAME=VALUE` argument. After an invocation exits non-zero, only teardowns run. The
result is the exit code of the first invocation other than a teardown that exited non-zero, and
when there is none, that of the first teardown that did, and otherwise {lit}`0`.
-/
def dispatchChain (entries : Array TestEntry) (links : List (List String))
    (helpers : Array Helper := #[]) (invocation : Array String := #[])
    (fixtures : Array FixtureEntry := #[]) : IO UInt32 := do
  let mut failure : Option UInt32 := none
  let mut teardownFailure : Option UInt32 := none
  let mut values : Array String := #[]
  for link in links do
    let teardown := isTeardown link
    if (failure.isSome || teardownFailure.isSome) && !teardown then continue
    let receives := link.head? == some "errata-run" || link.head? == some "errata-fixture"
    let link := if receives then link ++ values.toList else link
    let (c, value?) ← invoke entries link helpers invocation fixtures
    if let some (name, value) := value? then values := values.push s!"fixture:{name}={value}"
    unless c == 0 do
      if teardown then teardownFailure := teardownFailure <|> some c
      else failure := failure <|> some c
  return (failure <|> teardownFailure).getD 0

/-- Flushes the standard streams and ends the process with {name}`code`. -/
def exitNow (code : UInt8) : IO α := do
  try (← IO.getStdout).flush catch _ => pure ()
  try (← IO.getStderr).flush catch _ => pure ()
  -- `forceExit` skips the C library's cleanup of its streams, which can wait on the lock that a
  -- blocked read of standard input holds.
  IO.Process.forceExit code

/--
Ends the process group of this test executable, and exits with {lit}`1`, once its lifeline closes.
The lifeline is the executable's standard input. The process that started the executable holds the
other end of that pipe, which closes when that process exits, however it exits.
-/
def exitWhenStdinCloses (parentIn : IO.FS.Stream) : IO Unit := do
  -- Each read blocks until a line arrives or the pipe closes, so the thread sleeps for the length of
  -- the run. The process that starts the test executable leaves the pipe empty, so the first read
  -- returns when the pipe closes; a line that arrives anyway is skipped.
  repeat
    if (← parentIn.getLine).isEmpty then break
  try ProcessControl.killOwnGroup catch _ => pure ()
  exitNow 1

/--
The main of a test executable made by the Lean harness, over the tests in {name}`entries`.

{lit}`errata-list <out>` writes the inventory to the file {lit}`out`: the {lit}`protocol` record,
then a {lit}`setting` record for each setting that the tests and their fixtures take, with its
docstring as its description and its declared default, then a {lit}`fixture` record for each
fixture in {name}`fixtures` that the tests use, directly or through other fixtures, with its
docstring, the settings and fixtures it takes, and the threads it asks for, then a {lit}`test`
record per test with its fully qualified name, the name's components as its path, its file, line,
and column, its docstring as its description, its tags, and the settings and fixtures it takes.

{lit}`errata-run <out> <name> [setting:NAME=VALUE]... [fixture:NAME=VALUE]... [threads:N]` runs
the test with that name and writes its records to {lit}`out`. It exits with {lit}`0` when the test
passes and {lit}`1` otherwise. The test receives the settings and the fixtures' values, and parses
the values of those it takes. If a setting or a fixture it takes has no value, or a parser rejects
a value, the test ends with an error. Its context holds the thread grant, {lit}`1` without one.
When tests run concurrently, the runner also sets {lit}`LEAN_NUM_THREADS` to the grant, which sizes
the executable's task pool and reaches the processes it starts; when one test runs at a time, the
variable is left as it is, and the test uses the machine.

{lit}`errata-fixture <out> <name> setup|prepare|teardown [setting:NAME=VALUE]...
[fixture:NAME=VALUE]... [threads:N]` runs that phase of the fixture with that name, with the
settings and the values of the fixtures it takes, and its own value, from the setup, as its
{lit}`fixture:` argument. The setup writes its value as a {lit}`value` record, and failed phases
write a {lit}`verdict`. It exits with {lit}`0` when the phase succeeds and {lit}`1`
otherwise; for an unknown fixture it writes an error verdict and exits with {lit}`1`.

The runner passes {lit}`setting:Errata.updateGolden=true` for {lit}`--update-golden`, which the
harness reads itself to rewrite golden files. When the environment variable
{lit}`ERRATA_LIFELINE` is {lit}`1`, as the runner sets it, the executable's standard input is its
lifeline: when the pipe closes, the executable ends its own process group and exits. Otherwise the
command runs by hand with any standard input, {lit}`/dev/null` included. The test itself reads an
empty standard input. The runner holds the other end of setups' standard inputs until their
fixtures' teardowns end, and of prepares' until the tests they prepared end, so processes that a
setup or a prepare starts and that inherit its standard input read its end then, or when the run
ends, however the runner ends. Tests' and teardowns' standard inputs close when they end.

The runner also sets {lit}`ERRATA_DIR` to the directory of Errata's sources, where the shell
harness lives, and {lit}`ERRATA_RUN_ID` to the run's identifier, which is the same for every process
of one run and differs between runs, so that tests can do work once per run. Tests read both from
their environments.

{lit}`errata-helper <name> [ARG]...` runs the helper in {name}`helpers` with that name, passing it the
arguments that follow, and exits with the helper's exit code, which the process that started it sees
modulo 256, as the operating system reports it. The helper runs with the process's own standard
input, output, and error. This mode belongs to the Lean harness, and
{name (scope := "Errata")}`runHelper` starts it from inside a test. For an unknown name, the
executable writes a message to standard error and exits with {lit}`2`.

Several {lit}`errata-list`, {lit}`errata-run`, and {lit}`errata-fixture` invocations may be
chained, each separated by a {lit}`;` argument. The executable performs them in order, adds the
value that each setup produces to the later invocations as that fixture's {lit}`fixture:` argument,
runs only teardowns after an invocation that exits non-zero, and exits with the status of the first
invocation other than a teardown that exited non-zero, or else with that of the first teardown that
did.

With any other arguments, the executable prints its usage and exits with {lit}`2`.

{name}`invocation` is the command that starts this test executable, which the helpers of tests and
fixture phases run through. The compiled test executable leaves it empty, which stands for the
program's own path; the interpreted product gives the interpreter with its modules.
-/
def main (entries : Array TestEntry) (args : List String) (helpers : Array Helper := #[])
    (invocation : Array String := #[]) (fixtures : Array FixtureEntry := #[]) : IO UInt32 := do
  match args with
  | "errata-helper" :: _ => dispatch entries args helpers invocation fixtures
  | _ =>
    let links := chainLinks args
    unless links.any (fun l => l.head? == some "errata-run" || l.head? == some "errata-fixture") do
      return ← dispatchChain entries links helpers invocation fixtures
    -- The read blocks on a thread of its own, which it holds for the length of the run.
    if (← IO.getEnv "ERRATA_LIFELINE") == some "1" then
      let _ ← IO.asTask (prio := .dedicated) (exitWhenStdinCloses (← IO.getStdin))
    -- The main thread, where the test runs, reads an empty standard input from here on.
    discard <| IO.setStdin (IO.FS.Stream.ofBuffer (← IO.mkRef {}))
    let code ← try dispatchChain entries links helpers invocation fixtures catch e => do
      IO.eprintln s!"uncaught exception: {e}"
      pure 1
    -- The thread that reads standard input runs until the pipe closes, and a Lean program that
    -- returns from `main` waits for its threads, so the process is ended here.
    exitNow code.toUInt8
