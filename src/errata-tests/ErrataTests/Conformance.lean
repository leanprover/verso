/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The conformance suite: the runner, driven as a library, runs test executables and reports how each of
their tests ended. The checks that apply to any test executable run against the products of every
harness: a script that speaks the protocol by itself, a script on Errata's shell harness, a pytest
suite on Verso's pytest harness, and this library's own Lean test executable. The checks that need a
scripted behavior, such as a test that sleeps forever or contradicts its exit code, run against the
two shell scripts. Each test executable under `fixtures/harness` shows the runner one way that a test
can end.
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

/-- What a run reported: the report, the lines of its events file, and its human-readable lines. -/
structure Run where
  /-- The report. -/
  report : RunReport
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
another.
-/
def runWith (exes : Array ExecutableConfig) (opts : Options := {}) (config : Config := {}) :
    IO Run := do
  let events ← IO.mkRef #[]
  let lines ← IO.mkRef #[]
  let dir := config.errataDir? <|> some (← errataDir).toString
  let report ← execute { config with executables := exes, errataDir? := dir } opts
    { event := fun j => events.modify (·.push j), line := fun l => lines.modify (·.push l) }
  return { report, events := ← events.get, lines := ← lines.get }

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

/-- Every product. -/
def products : Array Product := #[basicProduct, errataShProduct, pytestProduct, leanProduct]

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
Starts the product's test executable by hand with the given arguments, as the runner would, and
returns what it wrote.
-/
def Product.invoke (p : Product) (args : Array String) : IO IO.Process.Output := do
  p.check
  let some cmd := p.exe.command[0]? | throw <| IO.userError "the command is empty"
  IO.Process.output {
    cmd, args := p.exe.command.extract 1 p.exe.command.size ++ args
    env := #[("ERRATA_DIR", some (← errataDir).toString), ("LEAN_ABORT_ON_PANIC", some "1")]
  }

/-- Runs {name}`check` against each product in {name}`ps`, as a named result per product. -/
def forEach (ps : Array Product) (check : Product → Test) : Test := do
  for p in ps do
    result p.name (check p)

/-! # Checks of every product -/

/--
The problems with an inventory: the {lit}`protocol` record must come first, and then the settings
before the tests; every setting and test has a name, no name appears twice, and every setting that a
test takes was declared before it.
-/
def inventoryProblems (records : Array Json) : Array String := Id.run do
  let mut problems := #[]
  if (records[0]?.bind (strField · "type")) != some "protocol" then
    problems := problems.push "the first record is not the protocol record"
  let mut settings : Array String := #[]
  let mut tests : Array String := #[]
  for r in records do
    match strField r "type" with
    | some "setting" =>
      let some name := strField r "name"
        | problems := problems.push s!"a setting without a name: {r.compress}"; continue
      unless tests.isEmpty do problems := problems.push s!"the setting {name} follows a test"
      if settings.contains name then problems := problems.push s!"the setting {name} is declared twice"
      settings := settings.push name
    | some "test" =>
      let some name := strField r "name"
        | problems := problems.push s!"a test without a name: {r.compress}"; continue
      if tests.contains name then problems := problems.push s!"the test {name} is listed twice"
      tests := tests.push name
      let deps := (r.getObjValAs? (Array Json) "settings").toOption.getD #[]
      for d in deps do
        let some s := strField d "name"
          | problems := problems.push s!"the test {name} takes a setting without a name"; continue
        unless settings.contains s do
          problems := problems.push s!"the test {name} takes the setting {s}, which is not declared before it"
    | _ => pure ()
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
Every product's inventory begins with the protocol record and declares its settings before its tests,
each with a name, none twice, and every setting a test takes declared before the test.
-/
@[test]
def inventoryWellFormed : Test := forEach products fun p => do
  let records ← p.inventory
  let problems := inventoryProblems records
  assertTrue problems.isEmpty s!"the inventory of {p.name} is malformed" (some ("\n".intercalate problems.toList))

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
    assertContains "the declared settings are Errata.seed, marker, note, greeting, needed"
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
test prints it. `--list` shows the default and what the test receives, and the command line wins
over the default.
-/
@[test]
def declaredDefaultReachesTest : Test := forEach products fun p => do
  let r ← p.run #[p.greets]
  let some res := r.result? p.greets.test | fail "no result"
  expectOutcome r p.greets.test (· matches .reported .pass) "a pass"
  assertTrue (res.settings.contains (p.greeting, "hello")) s!"the settings are {res.settings}"
  assertContains "hello" res.output.stdout
  result "--list shows it" do
    let r ← p.run #[p.greets] { list := true, seed := some 7 }
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
takes them, with the seed that the runner derives, and `--list` shows the derived seed.
-/
@[test]
def settingsArriveInOrder : Test := forEach scriptedProducts fun p => do
  let r ← p.runTests #["greets"] { seed := some 7 }
  let some res := r.result? "greets" | fail "no result"
  let seed := toString (testSeed 7 p.exe.name "greets")
  assertBEq s!"received setting:Errata.seed={seed}\nreceived setting:greeting=hello\n"
    res.output.stdout
  assertBEq #[("Errata.seed", seed), ("greeting", "hello")] res.settings
  result "--list shows the seed" do
    let r ← p.runTests #["greets"] { list := true, seed := some 7 }
    assertTrue (r.lines.contains s!"        Errata.seed = \"{seed}\"") s!"{r.lines}"
  result "--list without a run seed" do
    let r ← p.runTests #["greets"] { list := true }
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
    assertBEq 1 (← code.get)
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
A test that did not pass carries a command that reproduces it: its executable, {lit}`errata-run`, its
name, and its settings, quoted for a POSIX shell. Run in a shell, the command writes the test's
verdict to standard error and exits non-zero.
-/
@[test]
def reproductionLine : Test := do
  forEach products fun p => do
    let r ← p.run #[p.fails, p.passes]
    let some res := r.result? p.fails.test | fail "no result"
    let some cmd := res.reproduce? | fail "no reproduction line"
    assertContains s!"errata-run /dev/stderr {shellQuote p.fails.test}" cmd
    assertNotContains "  " cmd
    let out ← IO.Process.output { cmd := "bash", args := #["-c", cmd] }
    assertTrue (out.exitCode != 0) s!"the reproduction exited with 0: {cmd}"
    assertBEq #[some "fail"] ((verdictsIn out.stderr).map (strField · "status"))
    result "a pass has none" do
      assertTrue ((r.result? p.passes.test).bind (·.reproduce?)).isNone
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

/--
The profile's default filter selects the tests to run unless the command line gives filters, which
are joined by union.
-/
@[test]
def defaultFilterAndCommandLine : Test := do
  let config : Config := { profiles := #[{ name := "default", defaultFilter? := some { text := "tag(slow)" } }] }
  let ran (r : Run) : Array String := r.report.results.map (·.test)
  result "the default filter" do
    let r ← runWith #[basic ["pass", "sleeps"]] { timeoutMs? := some 300, gracePeriodMs? := some 100 } config
    assertBEq #["sleeps"] (ran r)
  result "the command line's filters" do
    let r ← runWith #[basic ["pass", "fail", "sleeps"]]
      { filters := #["name(=pass)", "name(=fail)"] } config
    assertBEq #["pass", "fail"] (ran r)
  result "a filter with a syntax error" do
    let r ← runWith #[basic ["pass"]] { filters := #["name(pass"] }
    assertTrue r.report.results.isEmpty "no test ran"
    let some issue := r.report.issues.find? (·.isError) | fail "no error"
    assertBEq "--filter:9: expected ')' to end the matcher" issue.message

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
Tests that run longer than `slow-after` are marked slow in the human report, and their outcomes
stand.
-/
@[test]
def slowTestsAreMarked : Test := do
  let config : Config := { profiles := #[{ name := "default", slowAfterMs? := some 0 }] }
  let r ← runWith #[basic ["pass"]] { verbosity := .verbose } config
  expectOutcome r "pass" (· matches .reported .pass) "a pass"
  assertTrue (r.lines.any fun l => l.endsWith "[slow]") s!"no line is marked slow: {r.lines}"
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
list value with a newline and a setting declared after a test, rejects `errata-fixture` and unknown
modes with exit code 2, and reports an undeclared test as an error.
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
    result "fixtures and usage" do
      assertExitCode 2 (← p.invoke #["errata-fixture", out.toString, "f", "setup"])
      assertExitCode 2 (← p.invoke #["errata-list"])
      assertExitCode 2 (← p.invoke #[])
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
as its path, its markers as its tags, its docstring, file, and line, and the settings it takes. It
runs one item and reports a failure with its message, location, and detail, and an error in a
fixture's setup as an error.
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
    assertBEq (some 28) (squares.getObjValAs? Nat "line").toOption
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
    assertBEq #["greeting", "needed"] settings
  result "a failure" do
    let r ← p.run #[p.fails]
    match r.outcome? p.fails.test with
    | some (.reported (.fail f)) =>
      assertBEq "AssertionError: the value is off" f.message
      assertBEq (some file) (f.location?.map (·.file))
      assertBEq (some 20) (f.location?.map (·.startPos.line))
      assertContains "assert value == 4" (f.detail?.getD "")
    | o => fail s!"expected a failure, got {repr o}"
  result "an error in setup" do
    let some e := p.errs? | fail "no erroring test"
    let r ← p.run #[e]
    match r.outcome? e.test with
    | some (.reported (.error m)) => assertContains "the fixture broke" m
    | o => fail s!"expected an error, got {repr o}"
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

end ErrataTests.Conformance
