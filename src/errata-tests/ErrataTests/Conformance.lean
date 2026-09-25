/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The conformance suite: the runner, driven as a library, runs test executables and reports how each of
their tests ended. The checks that apply to any test executable run against the products of every
harness: a script that speaks the protocol by itself, a script on Errata's shell harness, a pytest
suite on Verso's pytest harness, this library's own Lean test executable, and this library's tests
through the interpreted product of the Lean harness. The checks that need a scripted behavior, such
as a test that sleeps forever or contradicts its exit code, run against the two shell scripts. Each
test executable under `fixtures/harness` shows the runner one way that a test can end.
-/
module

public import Errata

open Errata
open Errata.Runner
open Lean (Json)

public section

namespace ErrataTests.Conformance

/-- The directory of the test executables that the suite runs. -/
def harnessDir : System.FilePath := "src/errata-tests/fixtures/harness"

/-- The string field {name}`key` of an event. -/
def strField (e : Json) (key : String) : Option String :=
  (e.getObjValAs? String key).toOption

/-- The shell test executable with many tests, listing only the named ones. -/
def basic (tests : List String) : ExecutableConfig where
  name := "basic"
  command := #["bash", (harnessDir / "basic.sh").toString]
  env := #[("BASIC_TESTS", " ".intercalate tests)]

/--
What a run reported: the report, its exit code, the lines of its events file, and its
human-readable lines.
-/
structure Run where
  /-- The report. -/
  report : RunReport
  /-- The exit code. -/
  code : UInt32
  /-- The events, in the order the dispatcher sent them. -/
  events : Array Json
  /-- The lines of the human-readable report. -/
  lines : Array String

/--
The directory of Errata's sources, which the runner passes to test executables as
{lit}`ERRATA_DIR`.
-/
def errataDir : IO System.FilePath := IO.FS.realPath "src/errata"

/--
Runs the given test executables with the runner, collecting what it reports. {name}`config` gives
the rest of the configuration; the directory of Errata's sources is this workspace's unless it names
another. The pool has one slot unless {name}`opts` gives it more.
-/
def runWith (exes : Array ExecutableConfig) (opts : Options := {}) (config : Config := {}) :
    IO Run := do
  let events ← IO.mkRef #[]
  let lines ← IO.mkRef #[]
  let dir := config.errataDir? <|> some (← errataDir).toString
  let opts := { opts with jobs? := opts.jobs? <|> some 1 }
  let (report, code) ← execute { config with executables := exes, errataDir? := dir } opts
    { event := fun j => events.modify (·.push j), line := fun l => lines.modify (·.push l) }
  return { report, code, events := ← events.get, lines := ← lines.get }

/-- The outcome of the test with the given name. -/
def Run.outcome? (r : Run) (test : String) : Option Outcome :=
  (r.report.results.find? fun res => res.test == test && res.resultPath.isEmpty).map (·.outcome)

/-- The test's own result. -/
def Run.result? (r : Run) (test : String) : Option Result :=
  r.report.results.find? fun res => res.test == test && res.resultPath.isEmpty

/-- Asserts that the named test ended with an outcome that satisfies {name}`p`. -/
def expectOutcome (r : Run) (test : String) (p : Outcome → Bool) (what : String) : Test := do
  match r.outcome? test with
  | some o => assertTrue (p o) s!"{test}: expected {what}, got {repr o}"
  | none => fail s!"{test}: no result"

/-! # Products -/

/--
A test of a product that plays a part in a check: its name, and the settings that it needs to play
it.
-/
structure Role where
  /-- The test's name, as the product's inventory gives it. -/
  test : String
  /-- The settings that make the test play the part. -/
  sets : Array (String × String) := #[]

/--
The fixtures of a product and the tests that use them, which play the parts that the checks of
fixtures ask for. Each product has fixtures of the same shapes: `stamped`, whose value is the file
that its setting names, which its setup, prepares, and teardown stamp and its users stamp as they
start and end; one that fails in each phase; one that takes a setting and `stamped`; one whose setup
sleeps; and one that asks for three threads and prints its grant.
-/
structure FixtureRoles where
  /-- The fixture whose value is the stamp file. -/
  stamped : String
  /-- The setting that names the stamp file. -/
  stampFile : String
  /-- The fixture whose setup fails. -/
  setupFails : String
  /-- The fixture whose first prepare fails. -/
  prepareFails : String
  /-- The fixture whose teardown fails. -/
  teardownFails : String
  /-- The fixture that takes the greeting and `stamped`. -/
  dependent : String
  /-- The fixture whose setup sleeps. -/
  slowSetup : String
  /-- The fixture that asks for three threads. -/
  threaded : String
  /-- The settings that make the failing fixtures fail. -/
  failSets : Array (String × String) := #[]
  /-- The settings that make the sleeping setup sleep past a short timeout. -/
  sleepSets : Array (String × String) := #[]
  /-- The users of `stamped` alone among its users. -/
  exclusive : Array String
  /-- The users of `stamped` that share it. -/
  shared : Array String
  /-- The user of the fixture whose setup fails. -/
  afterSetupFailure : String
  /-- The two users of the fixture whose first prepare fails. -/
  afterPrepareFailure : Array String
  /-- The user of the fixture whose teardown fails. -/
  beforeTeardownFailure : String
  /-- The user of the fixture that takes a setting and a fixture. -/
  usesDependent : String
  /-- The user of the fixture whose setup sleeps. -/
  afterSlowSetup : String
  /-- The user of the fixture that asks for threads. -/
  usesThreaded : String
  /-- A user of `stamped` that fails, with the failing settings. -/
  failingUser : String
  /--
  A test that asks for three threads, shares `stamped`, stamps the file, and prints its grant,
  when the product has one.
  -/
  threadedTest? : Option String := none

/-- The fixtures and their users in the two shell scripts, which have the same names. -/
def shellFixtures : FixtureRoles where
  stamped := "stamped"
  stampFile := "stamp-file"
  setupFails := "setup-fails"
  prepareFails := "prepare-fails"
  teardownFails := "teardown-fails"
  dependent := "dependent"
  slowSetup := "slow-setup"
  threaded := "threaded"
  exclusive := #["exclusive-a", "exclusive-b"]
  shared := #["shared-a", "shared-b"]
  afterSetupFailure := "after-setup-failure"
  afterPrepareFailure := #["after-prepare-failure-a", "after-prepare-failure-b"]
  beforeTeardownFailure := "before-teardown-failure"
  usesDependent := "uses-dependent"
  afterSlowSetup := "after-slow-setup"
  usesThreaded := "uses-threaded"
  failingUser := "fails-with-fixture"
  threadedTest? := some "threaded-test"

/--
A test executable that the checks run against: a product of a harness, with the tests that play the
parts the checks ask for.
-/
structure Product where
  /-- The product's name in the named results of each check. -/
  name : String
  /-- The test executable. -/
  exe : ExecutableConfig
  /-- The reason that the product is unavailable here, when it is. -/
  unavailable : IO (Option String) := pure none
  /--
  The time, in milliseconds, that an invocation of the product takes to start before it runs
  anything, beyond what the other products take.
  -/
  startMs : Nat := 0
  /-- A test that passes. -/
  passes : Role
  /-- A test that fails with a verdict. -/
  fails : Role
  /-- A test that ends with an error, when the product has one. -/
  errs? : Option Role := none
  /-- A test that takes the setting with the default {lit}`hello` and prints its value. -/
  greets : Role
  /-- A setting whose declared default is {lit}`hello`. -/
  greeting : String
  /-- A test that takes the mandatory setting without a default. -/
  needsSetting : Role
  /-- A mandatory setting without a default. -/
  needed : String
  /-- A test that prints {lit}`run id: ` and the value of {lit}`ERRATA_RUN_ID`. -/
  printsRunId : Role
  /-- Whether the product is a shell script whose tests stage the scripted behaviors. -/
  scripted : Bool := false
  /-- The product's fixtures and their users. -/
  fixtures : FixtureRoles

/-- A shell script in the harness directory, with the tests of `basic.sh`. -/
def shellProduct (name script : String) : Product where
  name := name
  exe := { name, command := #["bash", (harnessDir / script).toString] }
  passes := { test := "pass" }
  fails := { test := "verdict-fail" }
  greets := { test := "greets" }
  greeting := "greeting"
  needsSetting := { test := "needs-setting" }
  needed := "needed"
  printsRunId := { test := "run-id" }
  scripted := true
  fixtures := shellFixtures

/-- `basic.sh`, which speaks the protocol by itself. -/
def basicProduct : Product := shellProduct "basic" "basic.sh"

/-- `on-errata-sh.sh`, which Errata's shell harness speaks the protocol for. -/
def errataShProduct : Product := shellProduct "on-errata-sh" "on-errata-sh.sh"

/-- The directory of the pytest suite that runs through Verso's pytest harness. -/
def pytestDir : String := "src/errata-tests/fixtures/harness/pytest"

/-- The node id of a test in the pytest suite. -/
def pytestTest (name : String) : Role := { test := s!"{pytestDir}/test_sample.py::{name}" }

/--
The pytest suite, run through Verso's pytest harness with the Python environment of Verso's browser
tests.
-/
def pytestProduct : Product where
  name := "pytest"
  exe := {
    name := "pytest"
    command := #["uv", "run", "--project", "browser-tests", "--extra", "test", "python",
      "browser-tests/errata_pytest.py", pytestDir]
  }
  unavailable := do
    if ← ProcessControl.commandExists "uv" then return none
    return some "uv is not on the PATH, and the pytest harness runs through it"
  passes := pytestTest "test_passes"
  fails := pytestTest "test_fails"
  errs? := some (pytestTest "test_errors")
  greets := pytestTest "test_greets"
  greeting := "greeting"
  needsSetting := pytestTest "test_needs_setting"
  needed := "needed"
  printsRunId := pytestTest "test_run_id"
  fixtures := {
    shellFixtures with
    exclusive := #[(pytestTest "test_exclusive_a").test, (pytestTest "test_exclusive_b").test]
    shared := #[(pytestTest "test_shared_a").test, (pytestTest "test_shared_b").test]
    afterSetupFailure := (pytestTest "test_after_setup_failure").test
    afterPrepareFailure :=
      #[(pytestTest "test_after_prepare_failure_a").test,
        (pytestTest "test_after_prepare_failure_b").test]
    beforeTeardownFailure := (pytestTest "test_before_teardown_failure").test
    usesDependent := (pytestTest "test_uses_dependent").test
    afterSlowSetup := (pytestTest "test_after_slow_setup").test
    usesThreaded := (pytestTest "test_uses_threaded").test
    failingUser := (pytestTest "test_fails_with_fixture").test
    threadedTest? := none }

/-- The built test executable of this library, a product of the Lean harness. -/
def leanExe : System.FilePath := ".lake/build/bin/errata-test-ErrataTests"

/-- This library's own test executable. -/
def leanProduct : Product where
  name := "lean"
  exe := { name := "ErrataTests", command := #[leanExe.toString] }
  unavailable := do
    if ← leanExe.pathExists then return none
    return some s!"the test executable is not built at {leanExe}"
  passes := { test := "onePlusOne" }
  fails := { test := "ErrataTests.Roles.endsAsAsked", sets := #[("ErrataTests.Roles.outcome", "fail")] }
  errs? := some { test := "ErrataTests.Roles.endsAsAsked", sets := #[("ErrataTests.Roles.outcome", "error")] }
  greets := { test := "ErrataTests.Settings.greets" }
  greeting := "ErrataTests.Settings.greeting"
  needsSetting := { test := "ErrataTests.Roles.needsSetting" }
  needed := "ErrataTests.Roles.required"
  printsRunId := { test := "ErrataTests.Roles.printsRunId" }
  fixtures := {
    stamped := "ErrataTests.Resources.stamped"
    stampFile := "ErrataTests.Resources.stampFile"
    setupFails := "ErrataTests.Resources.setupFails"
    prepareFails := "ErrataTests.Resources.prepareFails"
    teardownFails := "ErrataTests.Resources.teardownFails"
    dependent := "ErrataTests.Resources.dependent"
    slowSetup := "ErrataTests.Resources.slowSetup"
    threaded := "ErrataTests.Resources.threaded"
    failSets := #[("ErrataTests.Resources.failing", "true")]
    sleepSets := #[("ErrataTests.Resources.sleepMs", "30000")]
    exclusive := #["ErrataTests.Resources.exclusiveA", "ErrataTests.Resources.exclusiveB"]
    shared := #["ErrataTests.Resources.sharedA", "ErrataTests.Resources.sharedB"]
    afterSetupFailure := "ErrataTests.Resources.afterSetupFailure"
    afterPrepareFailure :=
      #["ErrataTests.Resources.afterPrepareFailureA", "ErrataTests.Resources.afterPrepareFailureB"]
    beforeTeardownFailure := "ErrataTests.Resources.beforeTeardownFailure"
    usesDependent := "ErrataTests.Resources.usesDependent"
    afterSlowSetup := "ErrataTests.Resources.afterSlowSetup"
    usesThreaded := "ErrataTests.Resources.usesThreaded"
    failingUser := "ErrataTests.Resources.failsWithFixture" }

/-- The built interpreted product of the Lean harness. -/
def interpreter : System.FilePath := ".lake/build/bin/errata-interpret"

/--
The search path for the interpreted product, relative to the workspace, where the tests run: this
workspace's build directory and those of the packages that the tests import.
-/
def interpreterLeanPath : String :=
  System.SearchPath.separator.toString.intercalate <|
    [".lake/build/lib/lean", ".lake/packages/plausible/.lake/build/lib/lean"]

/--
This library's tests through the interpreted product of the Lean harness, which imports the modules
that hold the tests that play the roles and use the fixtures.
-/
def interpretedProduct : Product := { leanProduct with
  name := "interpreted"
  exe := {
    name := "ErrataTests"
    command := #[interpreter.toString, "ErrataTests", "ErrataTests.Roles", "ErrataTests.Settings",
      "ErrataTests.Resources", "--"]
    env := #[("LEAN_PATH", interpreterLeanPath)]
  }
  unavailable := do
    if ← interpreter.pathExists then return none
    return some s!"the interpreted product is not built at {interpreter}"
  -- Each invocation imports the test modules first.
  startMs := 3000
}

/-- Every product. -/
def products : Array Product :=
  #[basicProduct, errataShProduct, pytestProduct, leanProduct, interpretedProduct]

/-- The products whose tests stage the scripted behaviors. -/
def scriptedProducts : Array Product := products.filter (·.scripted)

/-- Throws an error that gives the reason when the product is unavailable here. -/
def Product.check (p : Product) : IO Unit := do
  if let some why ← p.unavailable then
    throw <| IO.userError s!"the product {p.name} cannot run: {why}"

/--
Runs the product's tests that the roles name, with the settings the roles need besides those of
{name}`opts`.
-/
def Product.run (p : Product) (roles : Array Role) (opts : Options := {}) (config : Config := {}) :
    IO Run := do
  p.check
  let filters := roles.map fun r => s!"name(={Filter.escapeText r.test})"
  runWith #[p.exe] { opts with filters := opts.filters ++ filters, sets := opts.sets ++ roles.flatMap (·.sets) }
    config

/-- Runs the product's tests with the given names. -/
def Product.runTests (p : Product) (tests : Array String) (opts : Options := {}) (config : Config := {}) :
    IO Run :=
  p.run (tests.map ({ test := · })) opts config

/--
Starts the product's test executable by hand with the given arguments, as a person would, and returns
what it wrote, without the lifeline that the runner gives the test executables it starts.
-/
def Product.invoke (p : Product) (args : Array String) : IO IO.Process.Output := do
  p.check
  let some cmd := p.exe.command[0]? | throw <| IO.userError "the command is empty"
  IO.Process.output {
    cmd, args := p.exe.command.extract 1 p.exe.command.size ++ args
    -- The process reads no lifeline, as a command run by hand does.
    env := #[("ERRATA_DIR", some (← errataDir).toString), ("LEAN_ABORT_ON_PANIC", some "1"),
      ("ERRATA_LIFELINE", none)] ++ p.exe.env.map fun (k, v) => (k, some v)
  }

/-- Runs {name}`check` against each product in {name}`ps`, as a named result per product. -/
def forEach (ps : Array Product) (check : Product → Test) : Test := do
  for p in ps do
    result p.name (check p)

/-! # Checks of every product -/

/--
The problems with an inventory: the {lit}`protocol` record must come first, then the settings, then
the fixtures, then the tests; every setting, fixture, and test has a name, no name appears twice,
and every setting and fixture that a fixture or a test takes was declared before it.
-/
def inventoryProblems (records : Array Json) : Array String := Id.run do
  let mut problems := #[]
  if (records[0]?.bind (strField · "type")) != some "protocol" then
    problems := problems.push "the first record is not the protocol record"
  let mut settings : Array String := #[]
  let mut fixtures : Array String := #[]
  let mut tests : Array String := #[]
  for r in records do
    let kind := (strField r "type").getD ""
    unless kind == "setting" || kind == "fixture" || kind == "test" do continue
    let some name := strField r "name"
      | problems := problems.push s!"a {kind} without a name: {r.compress}"; continue
    match kind with
    | "setting" =>
      unless tests.isEmpty && fixtures.isEmpty do
        problems := problems.push s!"the setting {name} follows a fixture or a test"
      if settings.contains name then problems := problems.push s!"the setting {name} is declared twice"
      settings := settings.push name
    | "fixture" =>
      unless tests.isEmpty do problems := problems.push s!"the fixture {name} follows a test"
      if fixtures.contains name then problems := problems.push s!"the fixture {name} is declared twice"
      for f in (r.getObjValAs? (Array String) "fixtures").toOption.getD #[] do
        unless fixtures.contains f do
          problems := problems.push s!"the fixture {name} takes the fixture {f}, which is not declared before it"
      fixtures := fixtures.push name
    | _ =>
      if tests.contains name then problems := problems.push s!"the test {name} is listed twice"
      tests := tests.push name
      for d in (r.getObjValAs? (Array Json) "fixtures").toOption.getD #[] do
        let f := (strField d "name").getD ""
        unless fixtures.contains f do
          problems := problems.push s!"the test {name} uses the fixture {f}, which is not declared before it"
    for d in (r.getObjValAs? (Array Json) "settings").toOption.getD #[] do
      let some s := strField d "name"
        | problems := problems.push s!"the {kind} {name} takes a setting without a name"; continue
      unless settings.contains s do
        problems := problems.push s!"the {kind} {name} takes the setting {s}, which is not declared before it"
  if tests.isEmpty then problems := problems.push "the inventory lists no test"
  return problems

/-- The records of a product's inventory, from its list file. -/
def Product.inventory (p : Product) : TestM (Array Json) := do
  IO.FS.withTempDir fun dir => do
    let out := dir / "list.jsonl"
    IO.FS.writeFile out ""
    let r ← p.invoke #["errata-list", out.toString]
    assertExitCode 0 r
    let lines := (← IO.FS.readFile out).splitOn "\n" |>.filter (!·.trimAscii.isEmpty)
    let mut records := #[]
    for l in lines do
      match Json.parse l with
      | .ok j => records := records.push j
      | .error e => fail s!"the list file has a line that is not JSON: {e}" (some l)
    return records

/--
Every product's inventory begins with the protocol record and declares its settings, then its
fixtures, then its tests, each with a name, none twice, and every setting and fixture that a fixture
or a test takes declared before it. The fixtures record their settings, their fixtures, and the
threads they ask for.
-/
@[test]
def inventoryWellFormed : Test := forEach products fun p => do
  let records ← p.inventory
  let problems := inventoryProblems records
  assertTrue problems.isEmpty s!"the inventory of {p.name} is malformed" (some ("\n".intercalate problems.toList))
  let fixture (name : String) : TestM Json := do
    let some r := records.find? fun r =>
        strField r "type" == some "fixture" && strField r "name" == some name
      | fail s!"no fixture record for {name}"
    return r
  let dependent ← fixture p.fixtures.dependent
  assertBEq (some #[p.fixtures.stamped]) (dependent.getObjValAs? (Array String) "fixtures").toOption
  assertContains p.greeting ((dependent.getObjVal? "settings").toOption.map (·.compress) |>.getD "")
  assertBEq (some 3) ((← fixture p.fixtures.threaded).getObjValAs? Nat "threads").toOption

/--
Known passing tests pass, known failing tests fail, and tests that throw end with an error.
-/
@[test]
def knownTestsEndAsTheyShould : Test := forEach products fun p => do
  let roles := #[p.passes, p.fails]
  let r ← p.run roles
  expectOutcome r p.passes.test (· matches .reported .pass) "a pass"
  expectOutcome r p.fails.test (· matches .reported (.fail _)) "a failure"
  if let some e := p.errs? then
    let r ← p.run #[e]
    expectOutcome r e.test (· matches .reported (.error _)) "an error"

/--
Test executables asked for a test outside their inventory exit non-zero and write no passing
verdict.
-/
@[test]
def unknownTestNameFails : Test := forEach products fun p => do
  IO.FS.withTempDir fun dir => do
    let out := dir / "out.jsonl"
    IO.FS.writeFile out ""
    let r ← p.invoke #["errata-run", out.toString, "no-such-test"]
    assertTrue (r.exitCode != 0) "the exit code is not zero"
    assertNotContains "\"status\":\"pass\"" (← IO.FS.readFile out)
    assertNotContains "\"status\": \"pass\"" (← IO.FS.readFile out)

/--
Tests with mandatory settings that have no value are inconclusive, naming the setting, and the
runner starts no process for them. The rest of the run goes on.
-/
@[test]
def settingMissing : Test := forEach products fun p => do
  let r ← p.run #[p.needsSetting, p.passes]
  expectOutcome r p.needsSetting.test (· matches .inconclusive (.settingMissing _))
    s!"settingMissing {p.needed}"
  match r.outcome? p.needsSetting.test with
  | some (.inconclusive (.settingMissing s)) => assertBEq p.needed s
  | _ => pure ()
  let some res := r.result? p.needsSetting.test | fail "no result"
  assertNotContains "ran without its setting" res.output.all
  expectOutcome r p.passes.test (· matches .reported .pass) "a pass"
  result "a value from the command line lets it run" do
    let r ← p.run #[p.needsSetting] { sets := #[(p.needed, "yes")] }
    expectOutcome r p.needsSetting.test (· matches .reported .pass) "a pass"

/--
Values that the command line gives to settings that no test executable declares stop the run before
anything runs, with the declared settings in the message. Those that the profile gives are warnings,
since profiles serve every library's executable and runs may select some of them.
-/
@[test]
def undeclaredSettingRejected : Test := do
  forEach products fun p => do
    let r ← p.run #[p.passes] { sets := #[("nonsense", "1")] }
    assertTrue r.report.results.isEmpty "no test ran"
    let some issue := r.report.issues.find? (·.isError) | fail "no error"
    assertContains "--set gives the setting nonsense a value, and no test executable of this run \
      declares it" issue.message
    assertContains s!"the declared settings are " issue.message
    assertContains p.greeting issue.message
  result "the declared settings of basic.sh" do
    let r ← runWith #[basic ["pass"]] { sets := #[("nonsense", "1")] }
    let some issue := r.report.issues.find? (·.isError) | fail "no error"
    assertContains "the declared settings are Errata.seed, marker, note, greeting, needed, stamp-file"
      issue.message
  result "in a profile" do
    let config : Config := { profiles := #[{ name := "default", settings := #[("other", "x")] }] }
    let r ← runWith #[basic ["pass"]] {} config
    expectOutcome r "pass" (· matches .reported .pass) "a pass"
    let some issue := r.report.issues.find? (!·.isError) | fail "no warning"
    assertContains "the profile default gives the setting other a value" issue.message
    let r ← runWith #[basic ["pass"]] { wfail := true } config
    assertTrue r.report.failsRun "--wfail makes it an error"

/--
Settings' declared defaults reach the tests that take them when nothing else gives a value, and the
test prints it. `list -v` shows the default and what the test receives, and the command line wins
over the default.
-/
@[test]
def declaredDefaultReachesTest : Test := forEach products fun p => do
  let r ← p.run #[p.greets]
  let some res := r.result? p.greets.test | fail "no result"
  expectOutcome r p.greets.test (· matches .reported .pass) "a pass"
  assertTrue (res.settings.contains (p.greeting, "hello")) s!"the settings are {res.settings}"
  assertContains "hello" res.output.stdout
  result "list -v shows it" do
    let r ← p.run #[p.greets] { command := .list, verbosity := .quiet, seed := some 7 }
    assertTrue (r.lines.contains s!"  {p.greeting} (default \"hello\")") s!"{r.lines}"
    assertTrue (r.lines.contains s!"        {p.greeting} = \"hello\"") s!"{r.lines}"
    assertTrue r.report.results.isEmpty "nothing ran"
    assertTrue (!r.lines.any (·.endsWith "inconclusive")) "a listing has no summary line"
  result "the command line wins over the default" do
    let r ← p.run #[p.greets] { sets := #[(p.greeting, "hi")] }
    let some res := r.result? p.greets.test | fail "no result"
    assertContains "hi" res.output.stdout
    assertNotContains "hello" res.output.stdout

/--
The test that the shell scripts call `greets` receives its settings as arguments, in the order it
takes them, with the seed that the runner derives, and `list -v` shows the derived seed.
-/
@[test]
def settingsArriveInOrder : Test := forEach scriptedProducts fun p => do
  let r ← p.runTests #["greets"] { seed := some 7 }
  let some res := r.result? "greets" | fail "no result"
  let seed := toString (testSeed 7 p.exe.name "greets")
  -- `basic.sh` echoes every argument, the thread grant included.
  let grant := if p.exe.name == basicProduct.exe.name then "received threads:1\n" else ""
  assertBEq s!"received setting:Errata.seed={seed}\nreceived setting:greeting=hello\n{grant}"
    res.output.stdout
  assertBEq #[("Errata.seed", seed), ("greeting", "hello")] res.settings
  result "list -v shows the seed" do
    let r ← p.runTests #["greets"] { command := .list, verbosity := .quiet, seed := some 7 }
    assertTrue (r.lines.contains s!"        Errata.seed = \"{seed}\"") s!"{r.lines}"
  result "list -v without a run seed" do
    let r ← p.runTests #["greets"] { command := .list, verbosity := .quiet }
    assertTrue (r.lines.contains "        Errata.seed: derived from the run's seed") s!"{r.lines}"

/-! # Checks of the scripted products -/

/--
Tier 0: test executables that write no verdict are judged by their exit codes alone. Zero exits are
passes, and non-zero exits without a verdict are inconclusive, with the test's output kept.
-/
@[test]
def tierZeroPassAndFail : Test := forEach scriptedProducts fun p => do
  let r ← p.runTests #["silent", "fail"]
  result "a zero exit passes" do
    expectOutcome r "silent" (· matches .reported .pass) "a pass"
  result "a non-zero exit without a verdict" do
    expectOutcome r "fail" (· matches .inconclusive (.exitedWithoutVerdict 1)) "exitedWithoutVerdict 1"
    let some res := r.result? "fail" | fail "no result"
    assertContains "failing on purpose" res.output.stdout

/-- Tier 1: a verdict record says why a test failed. -/
@[test]
def tierOneVerdict : Test := forEach scriptedProducts fun p => do
  let r ← p.runTests #["pass", "verdict-fail"]
  expectOutcome r "pass" (· matches .reported .pass) "a pass"
  match r.outcome? "verdict-fail" with
  | some (.reported (.fail f)) => assertBEq "the check failed" f.message
  | o => fail s!"expected a failure with a message, got {repr o}"

/-- A run that writes nothing to its result file is accepted, with the verdict from its exit code. -/
@[test]
def silentRunAccepted : Test := do
  let r ← runWith #[basic ["silent"]]
  expectOutcome r "silent" (· matches .reported .pass) "a pass"
  assertTrue r.report.succeeded

/-- Records of unknown types, and unknown fields of known records, are ignored. -/
@[test]
def unknownRecordsIgnored : Test := forEach scriptedProducts fun p => do
  let r ← p.runTests #["unknown-records"]
  expectOutcome r "unknown-records" (· matches .reported .pass) "a pass"

/--
Exit codes that contradict the reported verdict are mismatches, whichever way they go. On the shell
harness, tests that call `errata_fail` exit with 1, so the `mismatch-fail` test of
`on-errata-sh.sh` fails.
-/
@[test]
def verdictMismatch : Test := forEach scriptedProducts fun p => do
  let r ← p.runTests #["mismatch-pass", "mismatch-fail"]
  expectOutcome r "mismatch-pass" (· matches .inconclusive (.verdictMismatch 1 .pass))
    "verdictMismatch 1 pass"
  if p.exe.name == basicProduct.exe.name then
    expectOutcome r "mismatch-fail" (· matches .inconclusive (.verdictMismatch 0 (.fail _)))
      "verdictMismatch 0 fail"
  else
    expectOutcome r "mismatch-fail" (· matches .reported (.fail _)) "a failure"

/--
The shell harness runs a test's body with `set -e`, so a command that fails ends the test, and a
test that called `errata_fail` fails even when its body goes on and returns zero.
-/
@[test]
def shellHarnessEndsFailingTests : Test := do
  let r ← errataShProduct.runTests #["errexit", "fail-goes-on"]
  result "a failing command ends the test" do
    expectOutcome r "errexit" (· matches .inconclusive (.exitedWithoutVerdict 1))
      "exitedWithoutVerdict 1"
    let some res := r.result? "errexit" | fail "no result"
    assertNotContains "REACHED" res.output.all
  result "errata_fail fails the test" do
    match r.outcome? "fail-goes-on" with
    | some (.reported (.fail f)) => assertBEq "stopped here" f.message
    | o => fail s!"expected a failure, got {repr o}"
    let some res := r.result? "fail-goes-on" | fail "no result"
    assertContains "went on" res.output.stdout

/-- A non-zero exit code without a verdict is inconclusive, with the code. -/
@[test]
def exitedWithoutVerdict : Test := forEach scriptedProducts fun p => do
  let r ← p.runTests #["exits"]
  expectOutcome r "exits" (· matches .inconclusive (.exitedWithoutVerdict 3)) "exitedWithoutVerdict 3"
  let some res := r.result? "exits" | fail "no result"
  assertContains "about to exit" res.output.stderr

/-- A result file with a line that is not a record makes the outcome inconclusive. -/
@[test]
def resultStreamUnreadable : Test := forEach scriptedProducts fun p => do
  let r ← p.runTests #["garbled"]
  expectOutcome r "garbled" (· matches .inconclusive (.resultStreamUnreadable _))
    "resultStreamUnreadable"

/--
A test that runs past its timeout is terminated, and one that ignores the request is killed after the
grace period. Both are reported as timed out, with their output so far, and the JUnit report is still
written.
-/
@[test]
def timeoutEndsTests : Test := forEach scriptedProducts fun p => do
  p.check
  IO.FS.withTempDir fun dir => do
    let junit := dir / "report.xml"
    let filters := #["name(=sleeps)", "name(=stubborn)", "name(=pass)"]
    let opts : Options :=
      { timeoutMs? := some 300, gracePeriodMs? := some 300, junitPath := some junit.toString, filters }
    let code ← IO.mkRef (0 : UInt32)
    let config : Config := { executables := #[p.exe], errataDir? := some (← errataDir).toString }
    discard <| captureOutput do
      code.set (← executeAndWrite config opts)
    assertBEq ExitCode.testRunFailed (← code.get)
    let xml ← IO.FS.readFile junit
    result "terminated" do
      assertContains "type=\"timedOut\"" xml
      assertContains "timed out after" xml
      assertContains "going to sleep" xml
    result "the run goes on" do
      assertContains "<testcase name=\"pass\"" xml
  let r ← p.runTests #["sleeps", "stubborn"] { timeoutMs? := some 300, gracePeriodMs? := some 300 }
  result "a terminated test was not killed" do
    expectOutcome r "sleeps" (· matches .inconclusive (.timedOut _ false)) "timedOut, terminated"
  -- `basic.sh` ignores the request itself. On the shell harness the test's body runs in a subshell,
  -- which ignores it while the harness's own process ends, and the sweep of the process group ends
  -- the rest.
  if p.exe.name == basicProduct.exe.name then
    result "a test that ignores the request is killed" do
      expectOutcome r "stubborn" (· matches .inconclusive (.timedOut _ true)) "timedOut, killed"
  else
    result "a test that ignores the request times out" do
      expectOutcome r "stubborn" (· matches .inconclusive (.timedOut _ _)) "timedOut"

/-- A test that starts a process in the background and exits leaves no process running. -/
@[test]
def childProcessesEnded : Test := forEach scriptedProducts fun p => do
  let marker := toString (← IO.rand 0 (2 ^ 30))
  let r ← p.runTests #["spawns"] { sets := #[("marker", marker)] }
  expectOutcome r "spawns" (· matches .reported .pass) "a pass"
  let left ← IO.Process.output { cmd := "pgrep", args := #["-f", s!"errata-conformance-{marker}"] }
  assertTrue left.stdout.trimAscii.isEmpty s!"processes are left running: {left.stdout}"

/--
Every test executable receives {lit}`LEAN_ABORT_ON_PANIC=1`; a test that aborts is reported as ended
by a signal, and the rest of the run goes on.
-/
@[test]
def panicEndsOnlyItsTest : Test := forEach scriptedProducts fun p => do
  let r ← p.runTests #["panics", "pass"]
  expectOutcome r "panics" (· matches .inconclusive (.signaled 6)) "signaled 6"
  expectOutcome r "pass" (· matches .reported .pass) "a pass"

/-- A test executable that cannot be started to run a test is inconclusive for that test. -/
@[test]
def spawnFailure : Test := do
  IO.FS.withTempDir fun dir => do
    let script := dir / "vanishing.sh"
    IO.FS.writeFile script (← IO.FS.readFile (harnessDir / "vanishing.sh"))
    discard <| IO.Process.run { cmd := "chmod", args := #["+x", script.toString] }
    let r ← runWith #[{ name := "vanishing", command := #[script.toString] }]
    expectOutcome r "gone" (· matches .inconclusive (.spawnFailed _)) "spawnFailed"

/--
A test executable that leaves its list file empty is broken: the run stops before running anything,
with an error that names it and includes what it wrote to standard output.
-/
@[test]
def emptyListAborts : Test := do
  let exe : ExecutableConfig :=
    { name := "confused", command := #["bash", (harnessDir / "empty-list.sh").toString] }
  let r ← runWith #[exe, basic ["pass"]]
  assertTrue r.report.results.isEmpty "no test ran"
  assertTrue r.report.failsRun
  let some issue := r.report.issues.find? (·.isError) | fail "no error"
  assertContains "confused" issue.message
  assertContains "{\"type\":\"test\",\"name\":\"lost\"}" issue.message
  assertTrue (!(r.events.any fun e => strField e "name" == some "Run"))
    "the Run phase did not begin"

/-- The index of the first event that satisfies {name}`p`. -/
def firstIndex? (events : Array Json) (p : Json → Bool) : Option Nat :=
  events.findIdx? p

/-- Whether an event has the given type and, when given, the given value of a string field. -/
def isEvent (type : String) (field? : Option (String × String) := none) (e : Json) : Bool :=
  strField e "type" == some type &&
    match field? with
    | some (k, v) => strField e k == some v
    | none => true

/--
The events file starts with the protocol record and follows the dispatcher's order: the phases, then
for a test its start, its output and its named results, then its outcome, and the end last. Output
that the test executable printed follows the records that it wrote before printing it. Records that
the test executable wrote are forwarded with the executable's and the test's names.
-/
@[test]
def eventsInDispatcherOrder : Test := forEach scriptedProducts fun p => do
  let r ← p.runTests #["records"]
  let ev := r.events
  let idx (what : String) (p : Json → Bool) : TestM Nat := do
    let some i := firstIndex? ev p | fail s!"no {what} event"
    return i
  assertTrue (ev[0]?.map (isEvent "protocol") == some true) "the protocol record comes first"
  let list ← idx "List" (isEvent "phase" (some ("name", "List")))
  let run ← idx "Run" (isEvent "phase" (some ("name", "Run")))
  let start ← idx "start" (isEvent "start")
  let inside ← idx "inside" (isEvent "output" (some ("text", "inside\n")))
  let outside ← idx "outside" (isEvent "output" (some ("text", "outside\n")))
  let res ← idx "result" (isEvent "result")
  let outcome ← idx "outcome" (isEvent "outcome")
  let «end» ← idx "end" (isEvent "end")
  -- The output that the test executable printed after writing the `inside` record follows that
  -- record, and whether it precedes the named result's records depends on when they arrived.
  assertTrue (list < run && run < start && start < inside && inside < outside && start < res &&
    outside < outcome && res < outcome && outcome < «end») s!"events out of order: {ev.map (·.compress)}"
  assertBEq («end» + 1) ev.size
  assertTrue (strField ev[start]! "exe" == some p.exe.name &&
    strField ev[start]! "test" == some "records") "forwarded records are tagged"

/-- The events file that {lit}`--events` names holds the same events, one per line. -/
@[test]
def eventsFileWritten : Test := do
  IO.FS.withTempDir fun dir => do
    let path := dir / "events.jsonl"
    discard <| captureOutput do
      discard <| executeAndWrite { executables := #[basic ["pass"]] }
        { eventsPath := some path.toString }
    let lines := (← IO.FS.readFile path).splitOn "\n" |>.filter (!·.isEmpty)
    assertTrue (lines.all (Json.parse · |>.isOk)) "every line is JSON"
    assertContains "\"type\":\"protocol\"" (lines.headD "")
    assertContains "\"type\":\"end\"" (lines.getLastD "")

/-- The verdict records among the lines of {name}`text`, skipping lines that are not records. -/
def verdictsIn (text : String) : Array Json :=
  (text.splitOn "\n").toArray.filterMap fun l =>
    match Json.parse l with
    | .ok j => if isEvent "verdict" none j then some j else none
    | .error _ => none

/--
Tests that did not pass have commands that reproduce them: the executable, {lit}`errata-run`, the
test's name, its settings, and its thread grant, quoted for a POSIX shell. Run in a shell, each
command writes the test's verdict to standard error and exits with the test's status, 1.
-/
@[test]
def reproductionLine : Test := do
  forEach products fun p => do
    let r ← p.run #[p.fails, p.passes]
    let some res := r.result? p.fails.test | fail "no result"
    let some cmd := res.reproduce? | fail "no reproduction line"
    assertContains s!"errata-run /dev/stderr {shellQuote p.fails.test}" cmd
    -- One test runs at a time, so the line leaves the runtime's threads to the machine.
    assertNotContains "LEAN_NUM_THREADS" cmd
    assertContains " threads:1" cmd
    assertNotContains "  " cmd
    let out ← IO.Process.output
      { cmd := "bash", args := #["-c", cmd], env := #[("ERRATA_LIFELINE", none)] }
    assertBEq 1 out.exitCode
    assertBEq #[some "fail"] ((verdictsIn out.stderr).map (strField · "status"))
    result "a pass has none" do
      assertTrue ((r.result? p.passes.test).bind (·.reproduce?)).isNone
    result "with two slots, the line bounds the runtime's threads" do
      let r ← p.run #[p.fails] { jobs? := some 2 }
      let some cmd := (r.result? p.fails.test).bind (·.reproduce?) | fail "no reproduction line"
      assertContains "LEAN_NUM_THREADS=1 " cmd
  forEach scriptedProducts fun p => do
    let r ← p.runTests #["fail"] { sets := #[("note", "it's")] }
    let some cmd := (r.result? "fail").bind (·.reproduce?) | fail "no reproduction line"
    let script := p.exe.command[1]!
    assertContains s!"{script} errata-run /dev/stderr fail setting:Errata.seed=" cmd
    assertContains "'setting:note=it'\\''s'" cmd

/-- The arguments that run a role's test, with the settings it needs. -/
def Role.args (r : Role) (out : System.FilePath) : Array String :=
  #["errata-run", out.toString, r.test] ++ r.sets.map fun (k, v) => s!"setting:{k}={v}"

/--
Chains of invocations separated by {lit}`;` arguments run in order in one process, stop at the first
that exits non-zero, and exit with its status.
-/
@[test]
def chainsRunInOrder : Test := forEach products fun p => do
  IO.FS.withTempDir fun dir => do
    let out := dir / "out.jsonl"
    result "a chain stops at the first failure" do
      IO.FS.writeFile out ""
      let r ← p.invoke (p.passes.args out ++ #[";"] ++ p.fails.args out ++ #[";"] ++ p.passes.args out)
      assertTrue (r.exitCode != 0) "the chain exited with 0"
      assertBEq #[some "pass", some "fail"]
        ((verdictsIn (← IO.FS.readFile out)).map (strField · "status"))
    result "a chain that passes" do
      IO.FS.writeFile out ""
      let r ← p.invoke (p.passes.args out ++ #[";"] ++ p.passes.args out)
      assertExitCode 0 r
      assertBEq 2 (verdictsIn (← IO.FS.readFile out)).size

/--
Every test executable of one run receives the same {lit}`ERRATA_RUN_ID`, which is the run's
identifier in the report and in the events file's {lit}`protocol` record, and the next run's
identifier differs.
-/
@[test]
def runIdIsSharedWithinARun : Test := do
  for p in products do p.check
  let exes := products.map (·.exe)
  let filters := products.map fun p => s!"name(={Filter.escapeText p.printsRunId.test})"
  let runOnce : TestM (String × Array String) := do
    let r ← runWith exes { filters }
    let ids ← products.mapM fun p => do
      let some res := r.report.results.find? fun res =>
          res.exe == p.exe.name && res.test == p.printsRunId.test && res.resultPath.isEmpty
        | fail s!"{p.name}: no result"
      -- pytest prints the test's output after its own progress on the same line.
      let some rest := (res.output.stdout.splitOn "run id: ")[1]?
        | fail s!"{p.name}: no run id in its output" (some res.output.stdout)
      return ((rest.splitOn "\n").headD "").trimAscii.copy
    assertBEq (some r.report.runId) (r.events[0]?.bind (strField · "run_id"))
    return (r.report.runId, ids)
  let (first, ids) ← runOnce
  assertTrue (first.length == 16) s!"the run id is {first}"
  assertBEq (products.map fun _ => first) ids
  let (second, ids') ← runOnce
  assertTrue (second != first) "two runs have one identifier"
  assertBEq (products.map fun _ => second) ids'

/--
Test executables' result files begin with the {lit}`protocol` record. The runner reads result files
whose first record is another as unreadable.
-/
@[test]
def resultFileBeginsWithProtocol : Test := do
  forEach products fun p => do
    IO.FS.withTempDir fun dir => do
      let out := dir / "out.jsonl"
      IO.FS.writeFile out ""
      discard <| p.invoke (p.passes.args out)
      let first := (← IO.FS.readFile out).splitOn "\n" |>.headD ""
      match Json.parse first with
      | .ok j => assertBEq (some "protocol") (strField j "type")
      | .error e => fail s!"the first line is not JSON: {e}" (some first)
  result "a verdict before the protocol record" do
    let r ← runWith #[basic ["protocol-late"]]
    match r.outcome? "protocol-late" with
    | some (.inconclusive (.resultStreamUnreadable m)) =>
      assertContains "does not begin with a protocol record" m
    | o => fail s!"expected resultStreamUnreadable, got {repr o}"

/-- Shell quoting leaves safe words alone and single-quotes the rest. -/
@[test]
def shellQuoting : Test := do
  assertBEq "plain/path.sh" (shellQuote "plain/path.sh")
  assertBEq "'two words'" (shellQuote "two words")
  assertBEq "''" (shellQuote "")
  assertBEq "'it'\\''s'" (shellQuote "it's")

/-- Exit codes above 128 are read as signals. -/
@[test]
def signalExitCodes : Test := do
  assertBEq (some 6) (signalOfExitCode? 134)
  assertBEq (some 9) (signalOfExitCode? 137)
  assertBEq none (signalOfExitCode? 1)
  assertBEq none (signalOfExitCode? 128)

/--
Durations are sequences of whole numbers with units, in the order `h`, `m`, `s`, `ms` and each unit
at most once. The errors for malformed durations state the accepted form.
-/
@[test]
def durations : Test := do
  let valid : List (String × Nat) := [
    ("1s", 1000), ("10m", 600000), ("250ms", 250), ("90s", 90000), ("0s", 0), ("2m30s", 150000),
    ("1h30m", 5400000), ("1s500ms", 1500), ("1h2m3s4ms", 3723004), (" 2m30s ", 150000)]
  for (text, ms) in valid do
    result text do
      assertBEq (some ms) (parseDuration text).toOption
  let invalid := ["10", "fast", "30s2m", "2m2m", "2 m", "2.5m", "m", "", "1msms", "1s1ms1s"]
  for text in invalid do
    result (if text.isEmpty then "the empty string" else text) do
      match parseDuration text with
      | .ok ms => fail s!"parsed as {ms}ms"
      | .error e => assertContains durationForm e

/-- CPU lists count ranges and single CPUs. -/
@[test]
def cpuLists : Test := do
  assertBEq (some 4) (ProcessControl.countCpuList "0-3")
  assertBEq (some 6) (ProcessControl.countCpuList "0-3,8,10\n")
  assertBEq none (ProcessControl.countCpuList "3-1")

/-- Each test's seed is derived from the run's seed and the test's identity. -/
@[test]
def seedsAreDerived : Test := do
  assertBEq (testSeed 7 "e" "t") (testSeed 7 "e" "t")
  assertTrue (testSeed 7 "e" "t" != testSeed 7 "e" "u") "tests draw different seeds"
  assertTrue (testSeed 7 "e" "t" != testSeed 8 "e" "t") "runs draw different seeds"
  forEach scriptedProducts fun p => do
    let r ← p.runTests #["pass"] { seed := some 7 }
    let some outcome := r.events.find? (isEvent "outcome") | fail "no outcome"
    assertBEq (some (toString (testSeed 7 p.exe.name "pass"))) (strField outcome "seed")
    assertBEq 7 r.report.seed

/-- Unknown profiles stop the run, with the profiles in the message. -/
@[test]
def unknownProfile : Test := do
  let r ← runWith #[basic ["pass"]] { profile := "nightly" } { profiles := #[{ name := "ci" }] }
  assertTrue r.report.results.isEmpty "no test ran"
  let some issue := r.report.issues.find? (·.isError) | fail "no error"
  assertContains "no profile named nightly; its profiles are default, ci" issue.message
  assertBEq ExitCode.setupError r.code

/--
The command line's filter expressions, joined by union, select from the tests that the profile's
default filter selects, unless `--ignore-default-filter` draws them from the whole inventory; in a
filter expression, `default()` stands for the default filter. Command-line filters with syntax
errors end the run with the exit code of an invalid filter; filters of the configuration with syntax
errors, and default filters that contain `default()`, end it with that of a setup error.
-/
@[test]
def defaultFilterAndCommandLine : Test := do
  let config : Config := { profiles := #[{ name := "default", defaultFilter? := some { text := "tag(slow)" } }] }
  let ran (r : Run) : Array String := r.report.results.map (·.test)
  let quick : Options := { timeoutMs? := some 300, gracePeriodMs? := some 100 }
  result "the default filter" do
    let r ← runWith #[basic ["pass", "sleeps"]] quick config
    assertBEq #["sleeps"] (ran r)
  result "the command line's filters, within the default filter" do
    let r ← runWith #[basic ["pass", "fail", "sleeps"]]
      { quick with filters := #["name(=pass)", "name(=sleeps)"] } config
    assertBEq #["sleeps"] (ran r)
  result "--ignore-default-filter" do
    let r ← runWith #[basic ["pass", "fail", "sleeps"]]
      { filters := #["name(=pass)", "name(=fail)"], ignoreDefaultFilter := true } config
    assertBEq #["pass", "fail"] (ran r)
  result "default() in a filter" do
    let r ← runWith #[basic ["pass", "fail", "sleeps"]]
      { quick with filters := #["default() | name(=pass)"], ignoreDefaultFilter := true } config
    assertBEq #["pass", "sleeps"] (ran r)
  result "a filter with a syntax error" do
    let r ← runWith #[basic ["pass"]] { filters := #["name(pass"] }
    assertTrue r.report.results.isEmpty "no test ran"
    let some issue := r.report.issues.find? (·.isError) | fail "no error"
    assertBEq "--filter:9: expected ')' to end the matcher" issue.message
    assertBEq ExitCode.invalidFilter r.code
  result "default() in the default filter" do
    let dflt : FilterText := { text := "all() \\ default()" }
    let config : Config := { profiles := #[{ name := "default", defaultFilter? := some dflt }] }
    let r ← runWith #[basic ["pass"]] {} config
    assertTrue r.report.results.isEmpty "no test ran"
    assertBEq #["configuration:8: default() stands for the default filter, so the default filter \
      cannot contain it"] (r.report.issues.map (·.message))
    assertBEq ExitCode.setupError r.code
  result "a syntax error in the default filter" do
    let dflt : FilterText := { text := "tag(x" }
    let config : Config := { profiles := #[{ name := "default", defaultFilter? := some dflt }] }
    let r ← runWith #[basic ["pass"]] { filters := #["name(y"] } config
    assertBEq ExitCode.setupError r.code
    assertBEq 2 r.report.issues.size

/--
Name filters select the tests whose names contain one of them, and `--skip` leaves out the tests
whose names contain one of its patterns; under `--exact`, both match whole names. The name filters
select from what the filter expressions select.
-/
@[test]
def nameFiltersAndSkip : Test := do
  let exe := basic ["pass", "fail", "greets", "verdict-fail"]
  let ran (opts : Options) : IO (Array String) := do
    return (← runWith #[exe] opts).report.results.map (·.test)
  assertBEq #["fail", "verdict-fail"] (← ran { nameFilters := #["fail"] })
  assertBEq #["pass", "fail", "verdict-fail"] (← ran { nameFilters := #["fail", "pass"] })
  assertBEq #["fail"] (← ran { nameFilters := #["fail"], exact := true })
  assertBEq #["pass", "greets"] (← ran { skips := #["fail"] })
  assertBEq #["pass", "greets", "verdict-fail"] (← ran { skips := #["fail"], exact := true })
  assertBEq #["verdict-fail"] (← ran { nameFilters := #["fail"], filters := #["name(verdict)"] })

/--
Runs that select no test fail with the exit code 4 under `--no-tests fail`, the default; under
`--no-tests warn` they succeed with a warning, which `--wfail` makes fail as `fail` does; under
`--no-tests pass` they succeed without an issue.
-/
@[test]
def noTestsToRun : Test := do
  let none' : Options := { nameFilters := #["nothing has this name"] }
  result "fail" do
    let r ← runWith #[basic ["pass"]] none'
    assertBEq ExitCode.noTestsRun r.code
    assertBEq #[(true, noTestsMessage)] (r.report.issues.map fun i => (i.isError, i.message))
  result "warn" do
    let r ← runWith #[basic ["pass"]] { none' with noTests := .warn }
    assertBEq ExitCode.ok r.code
    assertBEq #[(false, "no tests to run")] (r.report.issues.map fun i => (i.isError, i.message))
  result "warn under --wfail" do
    let r ← runWith #[basic ["pass"]] { none' with noTests := .warn, wfail := true }
    assertBEq ExitCode.noTestsRun r.code
  result "pass" do
    let r ← runWith #[basic ["pass"]] { none' with noTests := .pass }
    assertBEq ExitCode.ok r.code
    assertTrue r.report.issues.isEmpty "no issue"
  result "a run with tests" do
    assertBEq ExitCode.ok (← runWith #[basic ["pass"]]).code
    assertBEq ExitCode.testRunFailed (← runWith #[basic ["pass", "fail"]]).code

/--
The summary counts the listed tests that the filters left out, as tests, then the libraries known to
have tests that the filters ruled out before building, as test libraries, and the configuration's
executables that they ruled out, each when it is not zero.
-/
@[test]
def skippedCounts : Test := do
  let summary (r : Run) : String := r.lines.back?.getD ""
  let exe := basic ["pass", "greets", "verdict-fail"]
  result "tests" do
    let r ← runWith #[exe] { nameFilters := #["pass"] }
    let expected := "1 passed, 0 failed, 0 errors, 0 inconclusive, 2 tests skipped"
    assertTrue ((summary r).endsWith expected)
      (summary r)
  result "none()" do
    let r ← runWith #[exe] { filters := #["none()"], noTests := .pass }
    assertTrue ((summary r).endsWith ", 3 tests skipped") (summary r)
  result "test libraries and executables" do
    let config : Config := {
      knownExecutables := #["basic", "Alpha", "Beta", "Empty", "gamma"]
      ruledOut := #["Alpha", "Beta", "Empty", "gamma"], skippedTestLibraries := #["Alpha", "Beta"]
      skippedExecutables := #["gamma"], partialSelection := true }
    let r ← runWith #[basic ["pass"]] {} config
    assertTrue
      ((summary r).endsWith ", 0 tests skipped, 2 test libraries skipped, 1 executable skipped")
      (summary r)
    let libsOnly := { config with skippedExecutables := #[], skippedTestLibraries := #["Alpha"] }
    let r ← runWith #[basic ["pass"]] {} libsOnly
    assertTrue ((summary r).endsWith ", 0 tests skipped, 1 test library skipped") (summary r)

/--
An `exe(…)` is judged against every test executable of the package, those that the filters ruled
out before building included, so filters that name or exclude a ruled-out executable draw no
warnings, under `--wfail` too.
-/
@[test]
def ruledOutExecutablesAreKnown : Test := do
  let config : Config := {
    knownExecutables := #["basic", "Alpha", "Beta"]
    ruledOut := #["Alpha", "Beta"], partialSelection := true }
  for filter in ["!exe(Alpha)", "exe(basic) | exe(Beta)"] do
    result filter do
      let r ← runWith #[basic ["pass"]] { filters := #[filter], wfail := true } config
      assertBEq #[] (r.report.issues.map (·.message))
      assertBEq ExitCode.ok r.code
  result "an executable that the package does not have" do
    let r ← runWith #[basic ["pass"]] { filters := #["exe(basic) | exe(Gamma)"] } config
    assertBEq #["--filter:13: exe(Gamma) matches no test executable"]
      (r.report.issues.map (·.message))

/--
The `list` command selects as a run does and runs nothing. Its human format names each executable
with a colon and its tests below it, indented by four spaces; the one-line format has a line per
test with the executable, the name, the file, and the tags; the JSON format holds the inventory with
what each test receives.
-/
@[test]
def listFormats : Test := do
  let exe := basic ["pass", "greets", "sleeps"]
  let dflt : FilterText := { text := "!tag(slow)" }
  let config : Config := { profiles := #[{ name := "default", defaultFilter? := some dflt }] }
  let listed (format : MessageFormat) : TestM Run := do
    let r ← runWith #[exe] { command := .list, messageFormat := format, seed := some 7 } config
    assertTrue r.report.results.isEmpty "nothing ran"
    assertBEq ExitCode.ok r.code
    return r
  result "human" do
    assertBEq #["basic:", "    pass", "    greets"] (← listed .human).lines
  result "oneline" do
    assertBEq #["basic  pass    basic.sh  [shell]", "basic  greets  basic.sh  [shell]"]
      (← listed .oneline).lines
  result "json" do
    let r ← listed .json
    let some text := r.lines[0]? | fail "no output"
    let .ok j := Json.parse text | fail s!"not JSON: {text}"
    assertBEq (some 2) (j.getObjValAs? Nat "selected").toOption
    assertBEq (some 1) (j.getObjValAs? Nat "skipped").toOption
    let some tests := (do
        let exes ← (j.getObjValAs? (Array Json) "executables").toOption
        (exes[0]?.bind fun e => (e.getObjValAs? (Array Json) "tests").toOption)) | fail "no tests"
    assertBEq #["pass", "greets"] (tests.filterMap (strField · "name"))
    let greets := tests[1]!
    let settings := greets.getObjValD "settings"
    assertBEq (some "hello") (settings.getObjValAs? String "greeting").toOption
  result "json-pretty" do
    let r ← listed .jsonPretty
    assertTrue (r.lines.any (·.contains '\n')) "the JSON is indented over several lines"
  result "human with settings, when the executables declare none" do
    let bare : ExecutableConfig := {
      name := "bare"
      command := #["bash", "-c", "printf '%s\\n' '{\"type\":\"protocol\",\"version\":1}' \
        '{\"type\":\"test\",\"name\":\"only\"}' >> \"$2\"", "bare"] }
    let r ← runWith #[bare] { command := .list, verbosity := .quiet }
    assertBEq #["bare:", "    only"] r.lines

/--
The source of a filter of {name}`length` characters in a one-line string of {name}`path` whose
opening delimiter is at {name}`line` and {name}`col`.
-/
private def oneLine (path : String) (line col length : Nat) : Filter.Source :=
  .file path line col ((Array.range (length + 1)).map ((line, col + 1 + ·)))

/--
Once the inventory is known, a `tag(…)` that matches no test's tag, an `exe(…)` that names no test
executable, and a filter that selects no test are warnings at their places, which `--wfail` makes
errors. The configuration's filters draw them only in a run of every test executable.
-/
@[test]
def filterWarnings : Test := do
  let r ← runWith #[basic ["pass"]] { filters := #["tag(fast) | exe(other)", "name(pass)"] }
  let warnings := r.report.issues.filter (!·.isError) |>.map (·.message)
  assertBEq #["--filter:0: tag(fast) matches no tag of any test",
    "--filter:12: exe(other) matches no test executable",
    "--filter:0: the filter selects no test"] warnings
  expectOutcome r "pass" (· matches .reported .pass) "a pass"
  result "a filter from the configuration names its place in the file" do
    let text : FilterText :=
      { text := "name(pass) | tag(fast)", source := oneLine "errata.toml" 3 16 22 }
    let config : Config := { profiles := #[{ name := "default", defaultFilter? := some text }] }
    let r ← runWith #[basic ["pass"]] {} config
    assertBEq #["errata.toml:3:30: tag(fast) matches no tag of any test"]
      (r.report.issues.map (·.message))
  result "--wfail" do
    let r ← runWith #[basic ["pass"]] { filters := #["tag(fast) | name(pass)"], wfail := true }
    assertTrue r.report.failsRun
  result "the configuration's filters in a run of some executables" do
    let text : FilterText :=
      { text := "all() \\ tag(browser)", source := oneLine "errata.toml" 3 16 20 }
    let override : Override := { filter := { text := "exe(elsewhere)" }, timeoutMs? := some 5000 }
    let config : Config := {
      profiles := #[{ name := "default", defaultFilter? := some text, overrides := #[override] }]
      partialSelection := true }
    let r ← runWith #[basic ["pass"]] { wfail := true } config
    assertBEq #[] (r.report.issues.map (·.message))
    expectOutcome r "pass" (· matches .reported .pass) "a pass"
    result "the command line's filters still warn" do
      let r ← runWith #[basic ["pass"]] { filters := #["tag(fast) | name(pass)"] } config
      assertBEq #["--filter:0: tag(fast) matches no tag of any test"]
        (r.report.issues.map (·.message))
    result "every executable" do
      let r ← runWith #[basic ["pass"]] {} { config with partialSelection := false }
      assertTrue (r.report.issues.any (·.message == "errata.toml:3:25: tag(browser) matches no tag of any test"))
        s!"{r.report.issues.map (·.message)}"

/-- Overrides' values apply to the tests their filters match; the first match wins per value. -/
@[test]
def overridesApply : Test := forEach scriptedProducts fun p => do
  let overrides : Array Override := #[
    { filter := { text := "name(=greets)" }, settings := #[("greeting", "first")] },
    { filter := { text := "tag(shell)" }, settings := #[("greeting", "second"), ("note", "override")] }]
  let profile : Profile := { name := "default", settings := #[("note", "profile")], overrides }
  let config : Config := { profiles := #[profile] }
  let r ← p.runTests #["greets"] {} config
  let some res := r.result? "greets" | fail "no result"
  assertContains "received setting:greeting=first\n" res.output.stdout
  assertBEq (some "override") ((res.settings.find? (·.1 == "note")).map (·.2))

/--
Resolution takes each setting from the command line, then the first matching override that gives
it, then the profile, then the declared default, and for `Errata.seed` the derived seed; the timeout
and grace period from the command line, the first matching override, the profile, and the
defaults; and the slow mark and golden updating from the first matching override, the profile, and
the defaults.
-/
@[test]
def resolutionPrecedence : Test := do
  let parse (text : String) : TestM SourcedFilter :=
    match SourcedFilter.parse text (.argument "test") with
    | .ok f => pure f
    | .error e => fail e
  let first : Override :=
    { filter := { text := "tag(a)" }, settings := #[("x", "first")], timeoutMs? := some 5 }
  let second : Override := {
    filter := { text := "all()" }, settings := #[("x", "second"), ("y", "second")]
    slowAfterMs? := some 7, timeoutMs? := some 6, updateGolden? := some true }
  let profile : Profile := {
    name := "p", settings := #[("x", "profile"), ("y", "profile"), ("z", "profile")]
    timeoutMs? := some 9, gracePeriodMs? := some 8, slowAfterMs? := some 11 }
  let ctx : ResolutionContext := {
    profile, overrides := #[(← parse "tag(a)", first), (← parse "all()", second)], runSeed := 3 }
  let declared : Array SettingInfo :=
    #[{ name := "w", default? := some "default" }, { name := "z", default? := some "default" }]
  let deps : Array Protocol.SettingDep :=
    #[{ name := "x" }, { name := "y" }, { name := "z" }, { name := "w" }, { name := seedSetting },
      { name := "v", optional := true }, { name := "u" }]
  let tagged : InventoryTest := { exeIdx := 0, name := "t", tags := #["a"], settings := deps }
  let plain : InventoryTest := { tagged with tags := #[] }
  let seed := toString (testSeed 3 "e" "t")
  result "the first matching override" do
    let r := ctx.resolve "e" declared tagged
    assertBEq
      #[("x", "first"), ("y", "second"), ("z", "profile"), ("w", "default"), (seedSetting, seed)]
      r.settings
    assertBEq #["u"] r.missing
    assertBEq true r.derivedSeed
    assertBEq 5 r.timeoutMs
    assertBEq 8 r.gracePeriodMs
    assertBEq 7 r.slowAfterMs
    assertBEq true r.updateGolden
  result "an override that matches another test" do
    let r := ctx.resolve "e" declared plain
    assertBEq (some "second") ((r.settings.find? (·.1 == "x")).map (·.2))
    assertBEq 6 r.timeoutMs
  result "the command line" do
    let ctx := { ctx with
      sets := #[("x", "cli"), (seedSetting, "12"), ("v", "given")], timeoutMs? := some 1
      gracePeriodMs? := some 2 }
    let r := ctx.resolve "e" declared tagged
    assertBEq (some "cli") ((r.settings.find? (·.1 == "x")).map (·.2))
    assertBEq (some "12") ((r.settings.find? (·.1 == seedSetting)).map (·.2))
    assertBEq false r.derivedSeed
    assertBEq (some "given") ((r.settings.find? (·.1 == "v")).map (·.2))
    assertBEq 1 r.timeoutMs
    assertBEq 2 r.gracePeriodMs
  result "the defaults" do
    let r := ({} : ResolutionContext).resolve "e" #[] { exeIdx := 0, name := "t" }
    assertBEq defaultTimeoutMs r.timeoutMs
    assertBEq defaultGracePeriodMs r.gracePeriodMs
    assertBEq defaultSlowAfterMs r.slowAfterMs
    assertBEq false r.updateGolden

/--
Tests that run longer than `slow-after` keep their outcome's status word in the human report, with
`[slow]` after the name, and their outcomes stand.
-/
@[test]
def slowTestsAreMarked : Test := do
  let config : Config := { profiles := #[{ name := "default", slowAfterMs? := some 0 }] }
  let r ← runWith #[basic ["pass"]] { verbosity := .verbose } config
  expectOutcome r "pass" (· matches .reported .pass) "a pass"
  assertTrue (r.lines.any fun l => l.startsWith "        PASS [" && l.endsWith "basic pass [slow]")
    s!"no line is marked slow: {r.lines}"
  assertTrue ((r.result? "pass").map (·.slow) == some true) "the result is slow"

/--
A test that writes records faster than the runner reads them is still stopped at its timeout, and
what it wrote after that is read for at most the grace period.
-/
@[test]
def fastWriterTimesOut : Test := forEach scriptedProducts fun p => do
  let start ← IO.monoMsNow
  let r ← p.runTests #["flood"] { timeoutMs? := some 1000, gracePeriodMs? := some 1000 }
  let wall := (← IO.monoMsNow) - start
  match r.outcome? "flood" with
  | some (.inconclusive (.timedOut ms _)) =>
    assertTrue (ms < 1000 + 1000 + 2000) s!"stopped only after {ms}ms"
  | o => fail s!"expected a timeout, got {repr o}"
  assertTrue (wall < 10000) s!"the run took {wall}ms"

/-- A second verdict record makes the result file unreadable, whatever the first one said. -/
@[test]
def twoVerdictsUnreadable : Test := forEach scriptedProducts fun p => do
  let r ← p.runTests #["twice"]
  match r.outcome? "twice" with
  | some (.inconclusive (.resultStreamUnreadable m)) => assertContains "two verdict records" m
  | o => fail s!"expected resultStreamUnreadable, got {repr o}"

/-- A test executable that takes longer than the timeout to list its tests stops the run. -/
@[test]
def listingTimesOut : Test := do
  let exe : ExecutableConfig :=
    { name := "slow", command := #["bash", (harnessDir / "slow-list.sh").toString] }
  let start ← IO.monoMsNow
  let r ← runWith #[exe] { timeoutMs? := some 500, gracePeriodMs? := some 300 }
  assertTrue ((← IO.monoMsNow) - start < 5000) "the listing was stopped"
  let some issue := r.report.issues.find? (·.isError) | fail "no error"
  assertContains "slow" issue.message
  assertContains "did not finish within 500ms" issue.message
  assertContains "listing slowly" issue.message

/--
A test executable exits after listing and leaves a process, in a session of its own, that holds its
output pipes. The run goes on within the pipe grace.
-/
@[test]
def listingPipesHeld : Test := do
  let marker := toString (← IO.rand 0 (2 ^ 30))
  let exe : ExecutableConfig :=
    { name := "escaping", command := #["bash", (harnessDir / "escaping-list.sh").toString]
      env := #[("MARKER", marker)] }
  let start ← IO.monoMsNow
  let r ← try runWith #[exe] { timeoutMs? := some 10000 }
    finally
      discard <| IO.Process.output { cmd := "pkill", args := #["-f", s!"errata-conformance-{marker}"] }
  assertTrue ((← IO.monoMsNow) - start < 5000) "the listing held up the run"
  expectOutcome r "listed" (· matches .reported .pass) "a pass"

/-- A test executable whose command does not exist stops the run, which names it. -/
@[test]
def missingCommand : Test := do
  let r ← runWith #[{ name := "absent", command := #["./no-such-test-executable"] }]
  let some issue := r.report.issues.find? (·.isError) | fail "no error"
  assertContains "absent could not list its tests: it could not be started" issue.message
  assertBEq ExitCode.listFailed r.code
  result "under list" do
    let r ← runWith #[{ name := "absent", command := #["./no-such-test-executable"] }]
      { command := .list }
    assertBEq ExitCode.listFailed r.code

/--
A signal that ends a test executable while it lists its tests stops the run with a message that
names the signal. A module initializer that panics ends the listing this way.
-/
@[test]
def listingSignaled : Test := do
  let r ← runWith #[{ name := "aborts", command := #["bash", "-c", "kill -ABRT $$", "aborts"] }]
  let some issue := r.report.issues.find? (·.isError) | fail "no error"
  assertContains "aborts could not list its tests: it was ended by signal 6 (exit code 134)"
    issue.message

/-! # The shell harness and the pytest harness -/

/-- The records of a result or list file, parsed. -/
def readRecords (path : System.FilePath) : TestM (Array Json) := do
  let lines := (← IO.FS.readFile path).splitOn "\n" |>.filter (!·.trimAscii.isEmpty)
  lines.toArray.mapM fun l => match Json.parse l with
    | .ok j => pure j
    | .error e => fail s!"a line that is not JSON: {e}" (some l)

/--
Errata's shell harness writes names and descriptions with any character as JSON strings, rejects a
list value with a newline, a setting declared after a test or a fixture, and a fixture declared after
a test, rejects unknown modes and phases with exit code 2, and reports an undeclared test or fixture
as an error. Prepares and teardowns without a function do nothing, and setups without one are
errors.
-/
@[test]
def shellHarness : Test := do
  let p := errataShProduct
  IO.FS.withTempDir fun dir => do
    let out := dir / "out.jsonl"
    -- Lists the tests of a script whose `errata_tests` has the given body.
    let listScript (body : String) : IO IO.Process.Output := do
      let script := dir / "misuse.sh"
      IO.FS.writeFile script <|
        "source \"$ERRATA_DIR/harnesses/errata.sh\"\n" ++ s!"errata_tests() \{ {body}; }\n" ++
        "errata_run_test() { :; }\nerrata_main \"$@\"\n"
      IO.FS.writeFile out ""
      IO.Process.output {
        cmd := "bash", args := #[script.toString, "errata-list", out.toString]
        env := #[("ERRATA_DIR", some (← errataDir).toString)]
      }
    result "a list value with a newline" do
      let r ← listScript "errata_test t --tags \"$(printf 'a\\nb')\""
      assertExitCode 2 r
      assertContains "holds a newline" r.stderr
    result "a setting declared after a test" do
      let r ← listScript "errata_test t; errata_setting_decl late \"A setting.\""
      assertExitCode 2 r
      assertContains "the setting late is declared after a test" r.stderr
    result "an unknown test" do
      IO.FS.writeFile out ""
      let r ← p.invoke #["errata-run", out.toString, "nothing"]
      assertExitCode 1 r
      let records ← readRecords out
      assertBEq (some "error") (records.back?.bind (strField · "status"))
      assertTrue (!records.any (isEvent "start")) "the unknown test did not start"
    result "an unknown fixture, an unknown phase, and usage" do
      assertExitCode 1 (← p.invoke #["errata-fixture", out.toString, "f", "setup"])
      assertExitCode 2 (← p.invoke #["errata-fixture", out.toString, "stamped", "clean"])
      assertExitCode 2 (← p.invoke #["errata-list"])
      assertExitCode 2 (← p.invoke #[])
    result "a fixture declared after a test" do
      let r ← listScript "errata_test t; errata_fixture_decl late \"A fixture.\""
      assertExitCode 2 r
      assertContains "the fixture late is declared after a test" r.stderr
    result "a setting declared after a fixture" do
      let script := dir / "late.sh"
      IO.FS.writeFile script <|
        "source \"$ERRATA_DIR/harnesses/errata.sh\"\n" ++
        "errata_fixtures() { errata_fixture_decl f \"A fixture.\"; errata_setting_decl s \"A setting.\"; }\n" ++
        "errata_main \"$@\"\n"
      IO.FS.writeFile out ""
      let r ← IO.Process.output {
        cmd := "bash", args := #[script.toString, "errata-list", out.toString]
        env := #[("ERRATA_DIR", some (← errataDir).toString)]
      }
      assertExitCode 2 r
      assertContains "the setting s is declared after a fixture" r.stderr
    result "a prepare and a teardown without a function" do
      let script := dir / "bare.sh"
      IO.FS.writeFile script <|
        "source \"$ERRATA_DIR/harnesses/errata.sh\"\n" ++
        "errata_fixtures() { errata_fixture_decl f \"A fixture.\"; }\n" ++
        "errata_main \"$@\"\n"
      let run (args : Array String) : IO IO.Process.Output := do
        IO.FS.writeFile out ""
        IO.Process.output {
          cmd := "bash", args := #[script.toString] ++ args
          env := #[("ERRATA_DIR", some (← errataDir).toString)]
        }
      assertExitCode 0 (← run #["errata-fixture", out.toString, "f", "prepare"])
      assertExitCode 0 (← run #["errata-fixture", out.toString, "f", "teardown"])
      assertExitCode 1 (← run #["errata-fixture", out.toString, "f", "setup"])
      assertContains "defines no errata_fixture_setup" (← IO.FS.readFile out)
    result "escaping" do
      let script := dir / "odd.sh"
      let name := "a \"quoted\"\\name\twith\ncontrol \x01 and é"
      IO.FS.writeFile script <|
        "source \"$ERRATA_DIR/harnesses/errata.sh\"\n" ++
        "errata_tests() { errata_test \"$(printf 'a \"quoted\"\\\\name\\twith\\ncontrol \\001 and é')\" " ++
        "--description \"$(printf 'one\\ntwo')\" --tags 'x,y z' --line 4; }\n" ++
        "errata_run_test() { :; }\nerrata_main \"$@\"\n"
      IO.FS.writeFile out ""
      let r ← IO.Process.output {
        cmd := "bash", args := #[script.toString, "errata-list", out.toString]
        env := #[("ERRATA_DIR", some (← errataDir).toString)]
      }
      assertExitCode 0 r
      let records ← readRecords out
      let some test := records.find? (isEvent "test") | fail "no test record"
      assertBEq (some name) (strField test "name")
      assertBEq (some "one\ntwo") (strField test "description")
      assertBEq (some #["x", "y z"]) (test.getObjValAs? (Array String) "tags").toOption
      assertBEq (some 4) (test.getObjValAs? Nat "line").toOption

/--
Verso's pytest harness lists each collected item with its node id as its name, the node id's parts
as its path, its markers as its tags, its docstring, file, and line, and the settings and Errata
fixtures it takes, after the settings and the fixtures that the items take. It runs one item and
reports a failure with its message, location, and detail, and an error in a pytest fixture's setup as
an error.
-/
@[test]
def pytestHarness : Test := do
  let p := pytestProduct
  let records ← p.inventory
  let find (test : String) : TestM Json := do
    let some r := records.find? (isEvent "test" (some ("name", s!"{pytestDir}/test_sample.py::{test}")))
      | fail s!"no record for {test}"
    return r
  let file := s!"{pytestDir}/test_sample.py"
  result "the inventory" do
    let squares ← find "test_squares[1]"
    assertBEq (some ((pytestDir.splitOn "/").toArray ++ #["test_sample.py", "test_squares[1]"]))
      (squares.getObjValAs? (Array String) "path").toOption
    assertBEq (some "A parameterized test.") (strField squares "description")
    assertBEq (some file) (strField squares "file")
    assertBEq (some 29) (squares.getObjValAs? Nat "line").toOption
    let inside ← find "TestGroup::test_inside"
    assertBEq (some #["TestGroup", "test_inside"])
      ((inside.getObjValAs? (Array String) "path").toOption.map fun a => a.extract (a.size - 2) a.size)
    let odd ← find "test_odd_id[a::b/c]"
    assertBEq (some "test_odd_id[a::b/c]")
      ((odd.getObjValAs? (Array String) "path").toOption.bind (·.back?))
    let marked ← find "test_marked"
    assertBEq (some #["chatty"]) (marked.getObjValAs? (Array String) "tags").toOption
    let greets ← find "test_greets"
    assertBEq (some "[{\"name\":\"greeting\",\"optional\":false}]")
      ((greets.getObjVal? "settings").toOption.map (·.compress))
    let settings := records.filter (isEvent "setting") |>.filterMap (strField · "name")
    assertBEq #["greeting", "needed", "stamp-file"] settings
    let fixtures := records.filter (isEvent "fixture") |>.filterMap (strField · "name")
    -- The inventory lists the fixtures that some test uses.
    assertBEq #["stamped", "setup-fails", "prepare-fails", "teardown-fails", "dependent",
      "slow-setup", "threaded"] fixtures
    let shared ← find "test_shared_a"
    assertBEq (some "[{\"exclusive\":false,\"name\":\"stamped\"}]")
      ((shared.getObjVal? "fixtures").toOption.map (·.compress))
    assertBEq none (shared.getObjValAs? (Array String) "tags").toOption
  result "a failure" do
    let r ← p.run #[p.fails]
    match r.outcome? p.fails.test with
    | some (.reported (.fail f)) =>
      assertBEq "AssertionError: the value is off" f.message
      assertBEq (some file) (f.location?.map (·.file))
      assertBEq (some 21) (f.location?.map (·.startPos.line))
      assertContains "assert value == 4" (f.detail?.getD "")
    | o => fail s!"expected a failure, got {repr o}"
  result "an error in setup" do
    let some e := p.errs? | fail "no erroring test"
    let r ← p.run #[e]
    match r.outcome? e.test with
    | some (.reported (.error m)) => assertContains "the fixture broke" m
    | o => fail s!"expected an error, got {repr o}"
  result "a phase that calls pytest.fail or sys.exit" do
    IO.FS.withTempDir fun dir => do
      let out := (dir / "out.jsonl").toString
      for (fixture, message) in [("calls-pytest-fail", "Failed: the setup gave up"),
          ("calls-exit", "the phase called sys.exit(3)")] do
        IO.FS.writeFile out ""
        let r ← p.invoke #["errata-fixture", out, fixture, "setup", ";", "errata-fixture", out,
          fixture, "teardown"]
        assertBEq 1 r.exitCode
        assertContains "teardown received no value" r.stdout
        let verdicts := verdictsIn (← IO.FS.readFile out)
        assertBEq #[some "error"] (verdicts.map (strField · "status"))
        assertBEq (some message) (verdicts[0]?.bind (strField · "message"))
  result "pytest's own error" do
    IO.FS.withTempDir fun dir => do
      let out := dir / "out.jsonl"
      IO.FS.writeFile out ""
      let r ← p.invoke (#["--no-such-flag"] ++ p.passes.args out)
      assertExitCode 1 r
      let verdicts := verdictsIn (← IO.FS.readFile out)
      assertBEq #[some "error"] (verdicts.map (strField · "status"))
      assertContains "pytest ended with exit code 4 (USAGE_ERROR) before it ran the test"
        ((verdicts[0]?.bind (strField · "message")).getD "")

/-! # Fixtures -/

/-- Runs a reproduction line in a shell, as a person would, without a lifeline. -/
def runLine (cmd : String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "bash", args := #["-c", cmd], env := #[("ERRATA_LIFELINE", none)] }

/-- The result of a fixture's phase, by the fixture's name and the phase's path. -/
def Run.fixtureResult? (r : Run) (fixture : String) (path : Array String) : Option Result :=
  r.report.results.find? fun res =>
    res.kind == .fixture && res.test == fixture && res.path == path && res.resultPath.isEmpty

/-- Asserts that a fixture's phase ended with an outcome that satisfies {name}`p`. -/
def expectPhase (r : Run) (fixture : String) (path : Array String) (p : Outcome → Bool)
    (what : String) : TestM Result := do
  let some res := r.fixtureResult? fixture path
    | fail s!"{path}: no result for the fixture's phase" (some s!"{r.report.results.map (·.path)}")
  assertTrue (p res.outcome) s!"{path}: expected {what}, got {repr res.outcome}"
  return res

/--
The problems with a stamp file's lines, in which each user of `stamped` writes `start NAME` and
`end NAME` and each prepare writes `prepare start` and `prepare end`: an exclusive user, whose name
mentions `exclusive`, or a user that asked for the whole pool, whose name mentions `threaded`, that
starts while another user or another user's prepare runs, and a user or a prepare that starts while
such a user runs. The second result says whether two users ran at once.
-/
def stampProblems (lines : Array String) : Array String × Bool := Id.run do
  let alone (n : String) : Bool := (n.find? "xclusive").isSome || (n.find? "threaded").isSome
  let mut running : Array String := #[]
  let mut problems := #[]
  let mut overlapped := false
  let mut preparing := 0
  for l in lines do
    if l == "prepare start" then
      if running.any alone then
        problems := problems.push s!"a prepare started while {running} ran alone"
      preparing := preparing + 1
    else if l == "prepare end" then
      preparing := preparing - 1
    else if let some name := l.dropPrefix? "start " then
      let name := name.copy
      if !running.isEmpty && alone name then
        problems := problems.push s!"{name} started while {running} ran"
      if running.any alone then
        problems := problems.push s!"{name} started while {running} ran alone"
      if alone name && preparing > 0 then
        problems := problems.push s!"{name} started while a prepare ran"
      if !running.isEmpty then overlapped := true
      running := running.push name
    else if let some name := l.dropPrefix? "end " then
      running := running.filter (· != name.copy)
  return (problems, overlapped)

/-- The lines of a file, without empty ones. -/
def fileLines (path : System.FilePath) : IO (Array String) := do
  return ((← IO.FS.readFile path).splitOn "\n").toArray.filter (!·.isEmpty)

/--
With two slots, the users of `stamped` alone among its users never overlap one another or its shared
users, and its shared users run at the same time. The setup comes first, a prepare ends before each
user starts, and the teardown comes last, once.
-/
@[test]
def exclusiveUsersNeverOverlap : Test := forEach products fun p => do
  IO.FS.withTempDir fun dir => do
    let stamps := dir / "stamps"
    let fx := p.fixtures
    let r ← p.runTests (fx.exclusive ++ fx.shared)
      { jobs? := some 2, sets := #[(fx.stampFile, stamps.toString)] }
    for t in fx.exclusive ++ fx.shared do
      expectOutcome r t (· matches .reported .pass) "a pass"
    let lines ← fileLines stamps
    let (problems, overlapped) := stampProblems lines
    assertTrue problems.isEmpty "users overlapped" (some ("\n".intercalate problems.toList))
    assertTrue overlapped s!"the shared users ran one after the other: {lines}"
    assertBEq (some "setup") lines[0]?
    assertBEq (some "teardown") (lines.back?.bind fun l => (l.splitOn " ")[0]?)
    assertBEq 1 (lines.filter (·.startsWith "setup")).size
    assertBEq 1 (lines.filter (·.startsWith "teardown")).size
    assertBEq 4 (lines.filter (· == "prepare end")).size
    discard <| expectPhase r fx.stamped #[fx.stamped, "setup"] (·.isPass) "a pass"
    discard <| expectPhase r fx.stamped #[fx.stamped, "teardown"] (·.isPass) "a pass"
    result "JUnit names fixtures' phases apart from tests" do
      let xml := junitReport r.report
      let classname := s!"classname=\"{xmlEscape fx.stamped} (fixture)\""
      assertContains s!"<testcase name=\"setup\" {classname}" xml
      assertContains s!"<testcase name=\"teardown\" {classname}" xml
      assertContains s!"<testcase name=\"prepare {xmlEscape fx.exclusive[0]!}\" {classname}" xml
    result "the events file has the phases' outcomes" do
      assertTrue (r.events.any fun e => isEvent "outcome" (some ("kind", "fixture")) e &&
        strField e "test" == some fx.stamped) "no outcome of a fixture's phase"

/--
If a setup fails, its fixture's users are reported as inconclusive without running, with the fixture
and the phase named, and its teardown still runs, without a value.
-/
@[test]
def setupFailureStopsUsers : Test := forEach products fun p => do
  let fx := p.fixtures
  let r ← p.runTests #[fx.afterSetupFailure, p.passes.test] { sets := fx.failSets }
  match r.outcome? fx.afterSetupFailure with
  | some (.inconclusive (.fixtureFailed f .setup)) => assertBEq fx.setupFails f
  | o => fail s!"expected fixtureFailed in the setup, got {repr o}"
  let some user := r.result? fx.afterSetupFailure | fail "no result"
  assertNotContains "received" user.output.all
  discard <| expectPhase r fx.setupFails #[fx.setupFails, "setup"] (!·.isPass) "a failure"
  let teardown ← expectPhase r fx.setupFails #[fx.setupFails, "teardown"] (·.isPass) "a pass"
  assertContains "teardown received no value" teardown.output.all
  expectOutcome r p.passes.test (· matches .reported .pass) "a pass"
  result "the reproduction line runs the chain" do
    let some cmd := user.reproduce? | fail "no reproduction line"
    let out ← runLine cmd
    assertBEq 1 out.exitCode
    assertBEq #[some "fail"] ((verdictsIn out.stderr).map (strField · "status"))
    -- The Lean harness writes what the phases print to their records, on standard error here.
    assertContains "teardown received no value" (out.stdout ++ out.stderr)
    assertNotContains "received fixture" (out.stdout ++ out.stderr)

/-- If a prepare fails, only the test it prepares stops, and the fixture's next user runs. -/
@[test]
def prepareFailureStopsOneTest : Test := forEach products fun p => do
  let fx := p.fixtures
  let r ← p.runTests fx.afterPrepareFailure { sets := fx.failSets }
  let (first, second) := (fx.afterPrepareFailure[0]!, fx.afterPrepareFailure[1]!)
  match r.outcome? first with
  | some (.inconclusive (.fixtureFailed f .prepare)) => assertBEq fx.prepareFails f
  | o => fail s!"expected fixtureFailed in the prepare, got {repr o}"
  expectOutcome r second (· matches .reported .pass) "a pass"
  discard <| expectPhase r fx.prepareFails #[fx.prepareFails, "prepare", first] (!·.isPass)
    "a failure"
  discard <| expectPhase r fx.prepareFails #[fx.prepareFails, "prepare", second] (·.isPass) "a pass"
  result "the reproduction line runs the chain" do
    let some cmd := (r.result? first).bind (·.reproduce?) | fail "no reproduction line"
    let out ← runLine cmd
    assertBEq 1 out.exitCode
    assertBEq #[some "fail"] ((verdictsIn out.stderr).map (strField · "status"))

/--
Tests that use a fixture and fail have reproduction lines that chain the fixture's setup, its
prepare, the test, and its teardown, and exit with the test's status.
-/
@[test]
def failingUserReproduces : Test := forEach products fun p => do
  IO.FS.withTempDir fun dir => do
    let fx := p.fixtures
    let stamps := dir / "stamps"
    let r ← p.runTests #[fx.failingUser]
      { sets := fx.failSets ++ #[(fx.stampFile, stamps.toString)] }
    expectOutcome r fx.failingUser (· matches .reported (.fail _)) "a failure"
    let some cmd := (r.result? fx.failingUser).bind (·.reproduce?) | fail "no reproduction line"
    IO.FS.writeFile stamps ""
    let out ← runLine cmd
    assertBEq 1 out.exitCode
    assertBEq #[some "fail"] ((verdictsIn out.stderr).map (strField · "status"))
    let lines ← fileLines stamps
    assertBEq #["setup", "prepare start", "prepare end"] (lines.extract 0 3)
    assertTrue (lines.size == 4 && lines[3]!.startsWith "teardown") s!"{lines}"

/-- If a teardown fails, it is reported on its own, after the test it served, which passes. -/
@[test]
def teardownFailureReportedAlone : Test := forEach products fun p => do
  let fx := p.fixtures
  let r ← p.runTests #[fx.beforeTeardownFailure] { sets := fx.failSets }
  expectOutcome r fx.beforeTeardownFailure (· matches .reported .pass) "a pass"
  discard <| expectPhase r fx.teardownFails #[fx.teardownFails, "teardown"] (!·.isPass) "a failure"
  let idx (test kind : String) : Option Nat := r.events.findIdx? fun e =>
    isEvent "outcome" (some ("kind", kind)) e && strField e "test" == some test &&
      (kind == "test" ||
        (e.getObjValAs? (Array String) "path").toOption.bind (·.back?) == some "teardown")
  match idx fx.beforeTeardownFailure "test", idx fx.teardownFails "fixture" with
  | some user, some teardown => assertTrue (user < teardown) "the teardown ran first"
  | _, _ => fail "an outcome is missing from the events"
  assertTrue (!r.report.succeeded) "the failed teardown fails the run"

/--
If its timeout stops a setup, the setup is inconclusive, its fixture's users are reported as
inconclusive without running, and its teardown still runs, without a value.
-/
@[test]
def killedSetupTearsDown : Test := forEach products fun p => do
  let fx := p.fixtures
  -- The timeout includes the product's start time, which the teardown pays as well.
  let config : Config := { profiles := #[{
    name := "default", fixtureTimeoutMs? := some (500 + p.startMs), gracePeriodMs? := some 300 }] }
  let start ← IO.monoMsNow
  let r ← p.runTests #[fx.afterSlowSetup] { sets := fx.sleepSets } config
  assertTrue ((← IO.monoMsNow) - start < 20000) "the setup was stopped"
  discard <| expectPhase r fx.slowSetup #[fx.slowSetup, "setup"]
    (· matches .inconclusive (.timedOut ..)) "a timeout"
  match r.outcome? fx.afterSlowSetup with
  | some (.inconclusive (.fixtureFailed f .setup)) => assertBEq fx.slowSetup f
  | o => fail s!"expected fixtureFailed in the setup, got {repr o}"
  let teardown ← expectPhase r fx.slowSetup #[fx.slowSetup, "teardown"] (·.isPass) "a pass"
  assertContains "teardown received no value" teardown.output.all

/--
The fixture `dependent`, which takes a setting and another fixture, receives both: its value joins
the greeting and the other fixture's value, which its user prints.
-/
@[test]
def fixturesReceiveSettings : Test := forEach products fun p => do
  IO.FS.withTempDir fun dir => do
    let fx := p.fixtures
    let stamps := (dir / "stamps").toString
    let r ← p.runTests #[fx.usesDependent]
      { sets := #[(p.greeting, "hi"), (fx.stampFile, stamps)] }
    expectOutcome r fx.usesDependent (· matches .reported .pass) "a pass"
    let some res := r.result? fx.usesDependent | fail "no result"
    assertContains s!"hi and {stamps}" res.output.all
    let setup ← expectPhase r fx.dependent #[fx.dependent, "setup"] (·.isPass) "a pass"
    assertBEq (some "hi") ((setup.settings.find? (·.1 == p.greeting)).map (·.2))

/--
The runner runs every phase of every fixture that a run needs, trivial phases included: each
fixture's setup once, its prepare before each of its users, and its teardown once, each of them a
pass. The fixture `dependent`, whose prepare and teardown are trivial, and `stamped`, which it takes
and whose prepare and teardown stamp a file, each serve one user here.
-/
@[test]
def everyPhaseRuns : Test := forEach products fun p => do
  IO.FS.withTempDir fun dir => do
    let fx := p.fixtures
    let users := #[fx.usesDependent, fx.exclusive[0]!]
    let r ← p.runTests users
      { sets := #[(p.greeting, "hi"), (fx.stampFile, (dir / "stamps").toString)] }
    for t in users do
      expectOutcome r t (· matches .reported .pass) "a pass"
    let phases (f : String) : Array (Array String) :=
      (r.report.results.filter fun res =>
        res.kind == .fixture && res.test == f && res.resultPath.isEmpty).map (·.path)
    assertBEq #[#[fx.dependent, "setup"], #[fx.dependent, "prepare", fx.usesDependent],
      #[fx.dependent, "teardown"]] (phases fx.dependent)
    let stamped := phases fx.stamped
    assertBEq 1 (stamped.filter (·[1]? == some "setup")).size
    assertBEq 1 (stamped.filter (·[1]? == some "teardown")).size
    for t in users do
      if fx.usesDependent != t then
        assertTrue (stamped.contains #[fx.stamped, "prepare", t]) s!"no prepare of stamped for {t}"
    for path in phases fx.dependent ++ stamped do
      discard <| expectPhase r path[0]! path (·.isPass) "a pass"

/--
Fixture phases and tests that ask for threads receive the grant as {lit}`threads:N` and as
{lit}`LEAN_NUM_THREADS`: the request when the pool has room for it, and the whole pool otherwise, in
which case the test runs alone.
-/
@[test]
def threadGrants : Test := forEach products fun p => do
  let fx := p.fixtures
  for (jobs, grant) in [(2, 2), (4, 3)] do
    result s!"with {jobs} slots" do
      let r ← p.runTests #[fx.usesThreaded] { jobs? := some jobs }
      let setup ← expectPhase r fx.threaded #[fx.threaded, "setup"] (·.isPass) "a pass"
      assertContains s!"threads: {grant}; LEAN_NUM_THREADS: {grant}" setup.output.all
  if let some test := fx.threadedTest? then
    result "a test that asks for more than the pool runs alone" do
      IO.FS.withTempDir fun dir => do
        let stamps := dir / "stamps"
        let r ← p.runTests (#[fx.shared[0]!, test] ++ fx.shared.extract 1)
          { jobs? := some 2, sets := #[(fx.stampFile, stamps.toString)] }
        let some res := r.result? test | fail "no result"
        assertContains "threads: 2; LEAN_NUM_THREADS: 2" res.output.all
        let lines ← fileLines stamps
        let (problems, _) := stampProblems lines
        assertTrue problems.isEmpty "users overlapped" (some ("\n".intercalate problems.toList))
        assertTrue (lines.contains s!"start {test}") s!"{lines}"

/--
Every invocation receives a thread grant: tests that ask for nothing receive {lit}`threads:1`. With
two slots they also receive {lit}`LEAN_NUM_THREADS=1`; with one slot the variable is absent,
whatever the runner's own environment holds.
-/
@[test]
def defaultThreadGrant : Test := forEach products fun p => do
  for (jobs, shown) in [(1, "LEAN_NUM_THREADS: \n"), (2, "LEAN_NUM_THREADS: 1\n")] do
    result s!"with {jobs} slots" do
      let r ← p.run #[p.printsRunId] { jobs? := some jobs }
      let some res := r.result? p.printsRunId.test | fail "no result"
      assertContains shown res.output.stdout
      unless p.name == pytestProduct.name do
        assertContains "threads: 1;" res.output.stdout

/-- Test executables asked for a fixture outside their inventory exit non-zero. -/
@[test]
def unknownFixtureFails : Test := forEach products fun p => do
  IO.FS.withTempDir fun dir => do
    let out := dir / "out.jsonl"
    IO.FS.writeFile out ""
    let r ← p.invoke #["errata-fixture", out.toString, "no-such-fixture", "setup"]
    assertTrue (r.exitCode != 0) "the exit code is not zero"
    assertNotContains "\"type\":\"value\"" (← IO.FS.readFile out)

/--
Chains of fixture phases and a test run in order in one process: each setup's value reaches the
later invocations, and once an invocation fails only teardowns run, without a value for fixtures
whose setups failed.
-/
@[test]
def fixtureChains : Test := forEach products fun p => do
  IO.FS.withTempDir fun dir => do
    let fx := p.fixtures
    let out := (dir / "out.jsonl").toString
    let stamps := dir / "stamps"
    let phase (f name : String) (extra : Array String := #[]) : Array String :=
      #["errata-fixture", out, f, name] ++ extra
    let settings := p.fixtures.failSets.map fun (k, v) => s!"setting:{k}={v}"
    result "a chain that passes" do
      let r ← p.invoke (phase fx.stamped "setup" #[s!"setting:{fx.stampFile}={stamps}"] ++ #[";"] ++
        phase fx.stamped "prepare" ++ #[";", "errata-run", out, fx.exclusive[0]!, ";"] ++
        phase fx.stamped "teardown")
      assertExitCode 0 r
      let lines ← fileLines stamps
      assertBEq #["setup", "prepare start", "prepare end"] (lines.extract 0 3)
      assertBEq (some "teardown") (lines.back?.bind fun l => (l.splitOn " ")[0]?)
      assertTrue (lines.any (·.startsWith "start ")) s!"the test ran: {lines}"
    result "teardowns after a failure" do
      let r ← p.invoke (phase fx.setupFails "setup" settings ++
        #[";", "errata-run", out, fx.afterSetupFailure, ";"] ++ phase fx.setupFails "teardown")
      -- The Lean harness writes what the phases print to their records.
      let printed := r.stdout ++ (← IO.FS.readFile out)
      assertContains "teardown received no value" printed
      assertNotContains "received fixture" printed
      result "the failed setup's status wins over the teardown's" do
        assertBEq 1 r.exitCode
    result "a failed teardown's status when everything else passed" do
      let r ← p.invoke (phase fx.teardownFails "setup" settings ++
        #[";", "errata-run", out, fx.beforeTeardownFailure, ";"] ++
        phase fx.teardownFails "teardown" settings)
      assertBEq 1 r.exitCode
    result "a passing teardown after a failed test" do
      let r ← p.invoke (phase fx.stamped "setup" ++ #[";"] ++ phase fx.stamped "prepare" ++
        #[";", "errata-run", out, fx.failingUser] ++
        fx.failSets.map (fun (k, v) => s!"setting:{k}={v}") ++ #[";"] ++
        phase fx.stamped "teardown")
      assertBEq 1 r.exitCode

/--
The runner's own lifeline, closed while a test that uses a fixture runs, cancels the run: the test
is ended, the fixture's teardown still runs, and the runner exits non-zero with no reports.
-/
@[test]
def cancelledRunTearsDown : Test := do
  let runnerExe : System.FilePath := ".lake/build/bin/errata-runner"
  unless ← runnerExe.pathExists do fail s!"the runner is not built at {runnerExe}"
  let script ← IO.FS.realPath (harnessDir / "basic.sh")
  IO.FS.withTempDir fun dir => do
    let stamps := dir / "stamps"
    let json := dir / "report.json"
    let exe : ExecutableConfig := {
      name := "basic", command := #["bash", script.toString]
      env := #[("BASIC_TESTS", "slow-user")] }
    let config : Config := { executables := #[exe], errataDir? := some (← errataDir).toString }
    let (config, workspace) ← config.write dir
    let child ← IO.Process.spawn {
      cmd := runnerExe.toString
      args := #[config.toString, workspace.toString, "--json", json.toString,
        "--grace-period", "500ms", "--set", s!"stamp-file={stamps}"]
      stdin := .piped, stdout := .piped, stderr := .piped
      env := #[("ERRATA_LIFELINE", some "1")]
    }
    let outTask ← IO.asTask (prio := .dedicated) child.stdout.readToEnd
    let errTask ← IO.asTask (prio := .dedicated) child.stderr.readToEnd
    let mut started := false
    for _ in [0 : 200] do
      if ← stamps.pathExists then
        if (← fileLines stamps).contains "start slow-user" then
          started := true
          break
      IO.sleep 50
    -- The standard input closes when its handle is dropped here.
    let (_, child) ← child.takeStdin
    let mut code? : Option UInt32 := none
    for _ in [0 : 400] do
      code? ← child.tryWait
      if code?.isSome then break
      IO.sleep 50
    if code?.isNone then child.kill
    let out := (← IO.wait outTask).toOption.getD ""
    let err := (← IO.wait errTask).toOption.getD ""
    assertTrue started "the test started" (some s!"stdout:\n{out}\nstderr:\n{err}")
    let some code := code? | fail "the runner did not exit"
    assertTrue (code != 0) "the runner exited non-zero"
    assertContains "standard input closed" err
    let lines ← fileLines stamps
    assertTrue (lines.back? == some "teardown") s!"no teardown after the cancellation: {lines}"
    assertTrue (!(← json.pathExists)) "no report was written"

/-! # Processes -/

/-- The runner built for this workspace. -/
def runnerExe : System.FilePath := ".lake/build/bin/errata-runner"

/-- Whether any process's command line contains {name}`text`. -/
def processesWith (text : String) : IO String := do
  return (← IO.Process.output { cmd := "pgrep", args := #["-f", text] }).stdout.trimAscii.copy

/--
When the lifeline of the built runner closes, the runner ends the test that is running, including a
process that the test started and that ignores the request to terminate. The runner then exits
non-zero, with no reports written.
-/
@[test]
def runnerLifeline : Test := do
  unless ← runnerExe.pathExists do fail s!"the runner is not built at {runnerExe}"
  let marker := toString (← IO.rand 0 (2 ^ 30))
  let script ← IO.FS.realPath (harnessDir / "basic.sh")
  IO.FS.withTempDir fun dir => do
    let json := dir / "report.json"
    let exe : ExecutableConfig :=
      { name := "basic", command := #["bash", script.toString], env := #[("BASIC_TESTS", "lingers pass")] }
    let (config, workspace) ← ({ executables := #[exe] } : Config).write dir
    let child ← IO.Process.spawn {
      cmd := runnerExe.toString
      args := #[config.toString, workspace.toString, "--json", json.toString,
        "--grace-period", "500ms", "--set", s!"marker={marker}"]
      stdin := .piped, stdout := .piped, stderr := .piped
      env := #[("ERRATA_LIFELINE", some "1")]
    }
    let outTask ← IO.asTask (prio := .dedicated) child.stdout.readToEnd
    let errTask ← IO.asTask (prio := .dedicated) child.stderr.readToEnd
    let mut started := false
    for _ in [0 : 200] do
      if !(← processesWith s!"errata-conformance-{marker}").isEmpty then
        started := true
        break
      IO.sleep 50
    -- The standard input closes when its handle is dropped here.
    let (_, child) ← child.takeStdin
    let mut code? : Option UInt32 := none
    for _ in [0 : 300] do
      code? ← child.tryWait
      if code?.isSome then break
      IO.sleep 50
    let left ← processesWith s!"errata-conformance-{marker}"
    unless left.isEmpty do
      discard <| IO.Process.output { cmd := "pkill", args := #["-9", "-f", s!"errata-conformance-{marker}"] }
    if code?.isNone then child.kill
    discard <| IO.wait outTask
    let err := (← IO.wait errTask).toOption.getD ""
    assertTrue started "the test started its background process"
    let some code := code? | fail "the runner did not exit"
    assertTrue (code != 0) "the runner exited non-zero"
    assertContains "standard input closed" err
    assertTrue left.isEmpty s!"processes survived: {left}"
    assertTrue (!(← json.pathExists)) "no report was written"

/--
Killing the process group of the driver, as the editor widget's cancel does, leaves no process of
the run: the runner is a member of the group and dies with it, and the interpreted test executable,
in a session of its own, ends its own group, with the process that its test started, when its
lifeline from the runner closes. A shell that starts the runner stands in for the driver.
-/
@[test]
def killingTheDriversGroupEndsTheRun : Test := do
  unless ← runnerExe.pathExists do fail s!"the runner is not built at {runnerExe}"
  interpretedProduct.check
  let marker := toString (← IO.rand 0 (2 ^ 30))
  IO.FS.withTempDir fun dir => do
    let (config, workspace) ← ({ executables := #[interpretedProduct.exe] } : Config).write dir
    let driver ← IO.Process.spawn {
      cmd := "bash"
      args := #["-c", "\"$@\"; exit $?", "driver", runnerExe.toString, config.toString,
        workspace.toString, "--filter", "name(=ErrataTests.Roles.lingers)",
        "--set", s!"ErrataTests.Roles.marker={marker}"]
      stdin := .piped, stdout := .piped, stderr := .piped, setsid := true
      env := #[("ERRATA_LIFELINE", some "1")]
    }
    let outTask ← IO.asTask (prio := .dedicated) driver.stdout.readToEnd
    let errTask ← IO.asTask (prio := .dedicated) driver.stderr.readToEnd
    let mut started := false
    for _ in [0 : 600] do
      if !(← processesWith s!"errata-conformance-{marker}").isEmpty then
        started := true
        break
      IO.sleep 50
    driver.kill
    discard driver.wait
    let mut left := ""
    for _ in [0 : 200] do
      left ← processesWith s!"errata-conformance-{marker}"
      if left.isEmpty then break
      IO.sleep 50
    unless left.isEmpty do
      discard <| IO.Process.output
        { cmd := "pkill", args := #["-9", "-f", s!"errata-conformance-{marker}"] }
    discard <| IO.wait outTask
    let err := (← IO.wait errTask).toOption.getD ""
    assertTrue started s!"the test started its process; the runner wrote:\n{err}"
    assertTrue left.isEmpty s!"processes survived: {left}"

/--
Through the interpreted product, a test runs its helpers through the interpreter with the same
modules: a helper that echoes its input and one that panics each behave as they do under the
compiled test executable.
-/
@[test]
def interpretedProductRunsHelpers : Test := do
  IO.FS.withTempDir fun dir => do
    for test in ["helpersRunInTheirOwnProcess", "arrayPanics"] do
      result test do
        let out := dir / s!"{test}.jsonl"
        let r ← interpretedProduct.invoke #["errata-run", out.toString, test]
        unless r.exitCode == 0 do
          fail s!"exited with {r.exitCode}" (some (r.stdout ++ r.stderr))
        assertBEq #[some "pass"] ((verdictsIn (← IO.FS.readFile out)).map (strField · "status"))

/-- The main that the driver generates for this library's compiled test executable. -/
def generatedMain : System.FilePath :=
  ".lake/errata-runner/ErrataGenerated_verso/ErrataTests.lean"

/--
The interpreted product lists a library's tests from the modules' {lit}`.olean` files, and its
inventory is the compiled test executable's, record for record, when it names the modules that the
compiled executable's generated main names, in the same order.
-/
@[test]
def interpretedInventoryIsCompiledInventory : Test := do
  interpretedProduct.check
  unless ← leanExe.pathExists do fail s!"the test executable is not built at {leanExe}"
  let main ← IO.FS.readFile generatedMain
  let some rest := (main.splitOn "getAllTests% \"verso\" ")[1]?
    | fail s!"{generatedMain} names no test modules" (some main)
  let modules := ((rest.splitOn ")")[0]!).splitOn " " |>.filter (!·.isEmpty)
  IO.FS.withTempDir fun dir => do
    let compiled := dir / "compiled.jsonl"
    let interpreted := dir / "interpreted.jsonl"
    assertExitCode 0 (← IO.Process.output
      { cmd := leanExe.toString, args := #["errata-list", compiled.toString] })
    assertExitCode 0 (← IO.Process.output {
      cmd := interpreter.toString
      args := modules.toArray ++ #["--", "errata-list", interpreted.toString]
      env := #[("LEAN_PATH", some interpreterLeanPath)] })
    let compiledLines := (← IO.FS.readFile compiled).splitOn "\n"
    let interpretedLines := (← IO.FS.readFile interpreted).splitOn "\n"
    assertTrue (compiledLines.length > 100)
      s!"the compiled inventory has {compiledLines.length} lines"
    for (c, i) in compiledLines.zip interpretedLines do
      assertBEq c i
    assertBEq compiledLines.length interpretedLines.length

/-- The lines of the list file that the interpreted product writes for {name}`modules`. -/
def interpretedList (modules : Array String) (chained : Bool := false) : TestM (Array String) := do
  IO.FS.withTempDir fun dir => do
    let out := dir / "list.jsonl"
    -- A chain imports the modules, as every invocation but a lone `errata-list` does.
    let chain := if chained then #[";", "errata-list", (dir / "again.jsonl").toString] else #[]
    let r ← IO.Process.output {
      cmd := interpreter.toString
      args := modules ++ #["--", "errata-list", out.toString] ++ chain
      env := #[("LEAN_PATH", some interpreterLeanPath)] }
    assertExitCode 0 r
    return ((← IO.FS.readFile out).splitOn "\n").toArray

/-- The records of the given type in the lines of a list file, decoded. -/
def recordsOfType (lines : Array String) (type : String) : Array Json :=
  lines.filterMap fun l => (Json.parse l).toOption.filter (strField · "type" == some type)

/--
The interpreted product lists from the {lit}`.olean` files only when {lit}`@[setting]` evaluated
the default of every setting that it lists, and imports the modules otherwise; either way it lists
what an import lists. In {lit}`ErrataTests.Defaults`, a default that calls a function of another
module, one that reads a value an {lit}`initialize` declaration holds, and one of a setting that
{lit}`attribute [setting]` marks in another module are left to the import, and both products list
them with the values that the tests receive. A test that {lit}`attribute [test]` marks in another
module than its declaration's lists its declaration's line.
-/
@[test]
def interpretedListingFallsBackToAnImport : Test := do
  interpretedProduct.check
  Lean.initSearchPath (← Lean.findSysroot) (System.SearchPath.parse interpreterLeanPath)
  result "the .olean files suffice" do
    let some _ ← unsafe OleanListing.listed? #[`ErrataTests.Settings, `ErrataTests.Resources]
      | fail "the listing needed an import"
    let fromFiles ← interpretedList #["ErrataTests.Settings", "ErrataTests.Resources"]
    let imported ←
      interpretedList #["ErrataTests.Settings", "ErrataTests.Resources"] (chained := true)
    assertBEq imported fromFiles
  result "an import is needed" do
    assertTrue (← unsafe OleanListing.listed? #[`ErrataTests.Defaults]).isNone
      "the listing read unevaluated defaults from the .olean file"
  result "the defaults listed" do
    let lines ← interpretedList #["ErrataTests.Defaults"]
    let defaults := (recordsOfType lines "setting").map fun s =>
      ((strField s "name").getD "", (strField s "default").getD "")
    assertBEq #[("ErrataTests.Defaults.imported", "n3"),
      ("ErrataTests.Defaults.initialized", "initial"),
      ("ErrataTests.Defaults.markedElsewhere", "d")] defaults
  result "a test marked in another module" do
    let lines ← interpretedList #["ErrataTests.Defaults"]
    let some t := (recordsOfType lines "test").find? fun t =>
        strField t "name" == some "ErrataTests.Defaults.testMarkedElsewhere"
      | fail "the test is not listed" (some ("\n".intercalate lines.toList))
    assertTrue ((t.getObjValAs? Nat "line").toOption.any (· > 0)) s!"{t.compress}"
  result "the tests receive the defaults" do
    let p := { interpretedProduct with
      exe.command := #[interpreter.toString, "ErrataTests.Defaults", "--"] }
    let tests := #["receivesImported", "receivesInitialized", "receivesMarkedElsewhere"].map
      (s!"ErrataTests.Defaults.{·}")
    let r ← p.runTests tests
    for test in tests do
      expectOutcome r test (· matches .reported .pass) "a pass"

/--
A test executable of the Lean harness, run by hand without {lit}`ERRATA_LIFELINE` and with
{lit}`/dev/null` as its standard input, runs the test.
-/
@[test]
def harnessRunsWithoutLifeline : Test := do
  unless ← leanExe.pathExists do fail s!"the test executable is not built at {leanExe}"
  IO.FS.withTempDir fun dir => do
    let out := dir / "out.jsonl"
    IO.FS.writeFile out ""
    let r ← IO.Process.output {
      cmd := leanExe.toString, args := #["errata-run", out.toString, "onePlusOne"]
      stdin := .null, env := #[("ERRATA_LIFELINE", none)]
    }
    assertExitCode 0 r
    assertContains "\"status\":\"pass\"" (← IO.FS.readFile out)

/-- The test executable with many trivial tests, {lean}`n` of them. -/
def manyTests (n : Nat) : IO ExecutableConfig := do
  let script ← IO.FS.realPath (harnessDir / "many.sh")
  return { name := "many", command := #["bash", script.toString]
           env := #[("ERRATA_MANY", toString n)] }

/--
The runner closes a test's files once the test has ended: with four slots and a limit of 256 open
files, as macOS gives a login shell, a run of 300 tests passes.
-/
@[test]
def runsUnderTheDefaultFileLimit : Test := do
  unless ← runnerExe.pathExists do fail s!"the runner is not built at {runnerExe}"
  IO.FS.withTempDir fun dir => do
    let config : Config :=
      { executables := #[← manyTests 300], errataDir? := some (← errataDir).toString }
    let (config, workspace) ← config.write dir
    let r ← IO.Process.output {
      cmd := "bash"
      args := #["-c", "ulimit -n 256 && exec \"$@\"", "runner", runnerExe.toString,
        config.toString, workspace.toString, "-j", "4"]
      env := #[("ERRATA_LIFELINE", none)] }
    assertExitCode 0 r
    assertContains "300 passed, 0 failed" r.stdout

/-- The number of files that the process {name}`pid` holds open, or {lean}`none` without `lsof`. -/
def openFiles (pid : UInt32) : IO (Option Nat) := do
  try
    let r ← IO.Process.output { cmd := "lsof", args := #["-p", toString pid] }
    if r.exitCode != 0 then return none
    return some ((r.stdout.splitOn "\n").filter (!·.isEmpty) |>.length)
  catch _ => return none

/--
Across a run of 100 tests with four slots, the files that the runner holds open stay within a bound
that the running tests' pipes and result files and the run's own files explain, whatever the number
of tests that have ended. The count is read with {lit}`lsof` where it is available.
-/
@[test]
def openFilesStayBounded : Test := do
  let pid ← IO.Process.getPID
  let some before ← openFiles pid | return
  let peak ← IO.mkRef before
  let running ← IO.mkRef true
  let sampler ← IO.asTask (prio := .dedicated) do
    while ← running.get do
      if let some n ← openFiles pid then peak.modify (max n)
      IO.sleep 100
  let r ← runWith #[← manyTests 100] { jobs? := some 4 }
  running.set false
  discard <| IO.wait sampler
  assertBEq 0 r.code
  assertBEq 100 (r.report.results.filter (·.outcome.isPass)).size
  -- Four running tests hold at most three pipes and a result file each.
  let most ← peak.get
  assertTrue (most ≤ before + 40)
    s!"the process held {before} files before the run and {most} at its peak"

end ErrataTests.Conformance
