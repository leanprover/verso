/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The conformance suite: the runner, driven as a library, runs test executables written in shell and
reports how each of their tests ended. Each test executable under `fixtures/harness` shows the runner
one way that a test can end.
-/
module

public import Errata

open Errata
open Errata.Runner
open Lean (Json)

public section

namespace ErrataTests.Conformance

/-- The directory of the shell test executables. -/
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
Runs the given test executables with the runner, collecting what it reports. {name}`config` gives
the rest of the configuration.
-/
def runWith (exes : Array ExecutableConfig) (opts : Options := {}) (config : Config := {}) :
    IO Run := do
  let events ← IO.mkRef #[]
  let lines ← IO.mkRef #[]
  let report ← execute { config with executables := exes } opts
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

/--
Tier 0: a test executable that writes nothing is judged by its exit code alone. A zero exit is a
pass, and a non-zero exit without a verdict is inconclusive, with the test's output kept.
-/
@[test]
def tierZeroPassAndFail : Test := do
  let r ← runWith #[basic ["silent", "fail"]]
  result "a zero exit passes" do
    expectOutcome r "silent" (· matches .reported .pass) "a pass"
  result "a non-zero exit without a verdict" do
    expectOutcome r "fail" (· matches .inconclusive (.exitedWithoutVerdict 1)) "exitedWithoutVerdict 1"
    let some res := r.result? "fail" | fail "no result"
    assertContains "failing on purpose" res.output.stdout

/-- Tier 1: a verdict record says why a test failed. -/
@[test]
def tierOneVerdict : Test := do
  let r ← runWith #[basic ["pass", "verdict-fail"]]
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
def unknownRecordsIgnored : Test := do
  let r ← runWith #[basic ["unknown-records"]]
  expectOutcome r "unknown-records" (· matches .reported .pass) "a pass"

/-- An exit code that contradicts the reported verdict is a mismatch, whichever way it goes. -/
@[test]
def verdictMismatch : Test := do
  let r ← runWith #[basic ["mismatch-pass", "mismatch-fail"]]
  expectOutcome r "mismatch-pass" (· matches .inconclusive (.verdictMismatch 1 .pass))
    "verdictMismatch 1 pass"
  expectOutcome r "mismatch-fail" (· matches .inconclusive (.verdictMismatch 0 (.fail _)))
    "verdictMismatch 0 fail"

/-- A non-zero exit code without a verdict is inconclusive, with the code. -/
@[test]
def exitedWithoutVerdict : Test := do
  let r ← runWith #[basic ["exits"]]
  expectOutcome r "exits" (· matches .inconclusive (.exitedWithoutVerdict 3)) "exitedWithoutVerdict 3"
  let some res := r.result? "exits" | fail "no result"
  assertContains "about to exit" res.output.stderr

/-- A result file with a line that is not a record makes the outcome inconclusive. -/
@[test]
def resultStreamUnreadable : Test := do
  let r ← runWith #[basic ["garbled"]]
  expectOutcome r "garbled" (· matches .inconclusive (.resultStreamUnreadable _))
    "resultStreamUnreadable"

/--
A test that runs past its timeout is terminated, and one that ignores the request is killed after the
grace period. Both are reported as timed out, with their output so far, and the JUnit report is still
written.
-/
@[test]
def timeoutEndsTests : Test := do
  IO.FS.withTempDir fun dir => do
    let junit := dir / "report.xml"
    let opts : Options :=
      { timeoutMs? := some 300, gracePeriodMs? := some 300, junitPath := some junit.toString }
    let code ← IO.mkRef (0 : UInt32)
    discard <| captureOutput do
      code.set (← executeAndWrite { executables := #[basic ["sleeps", "stubborn", "pass"]] } opts)
    assertBEq 1 (← code.get)
    let xml ← IO.FS.readFile junit
    result "terminated" do
      assertContains "type=\"timedOut\"" xml
      assertContains "timed out after" xml
      assertContains "going to sleep" xml
    result "the run goes on" do
      assertContains "<testcase name=\"pass\"" xml
  let r ← runWith #[basic ["sleeps", "stubborn"]] { timeoutMs? := some 300, gracePeriodMs? := some 300 }
  result "a terminated test was not killed" do
    expectOutcome r "sleeps" (· matches .inconclusive (.timedOut _ false)) "timedOut, terminated"
  result "a test that ignores the request is killed" do
    expectOutcome r "stubborn" (· matches .inconclusive (.timedOut _ true)) "timedOut, killed"

/-- A test that starts a process in the background and exits leaves no process running. -/
@[test]
def childProcessesEnded : Test := do
  let marker := toString (← IO.rand 0 (2 ^ 30))
  let r ← runWith #[basic ["spawns"]] { sets := #[("marker", marker)] }
  expectOutcome r "spawns" (· matches .reported .pass) "a pass"
  let left ← IO.Process.output { cmd := "pgrep", args := #["-f", s!"errata-conformance-{marker}"] }
  assertTrue left.stdout.trimAscii.isEmpty s!"processes are left running: {left.stdout}"

/--
Every test executable receives {lit}`LEAN_ABORT_ON_PANIC=1`; a test that aborts is reported as ended
by a signal, and the rest of the run goes on.
-/
@[test]
def panicEndsOnlyItsTest : Test := do
  let r ← runWith #[basic ["panics", "pass"]]
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

/-- A test executable asked for a test that it does not have exits non-zero without passing. -/
@[test]
def unknownTestNameFails : Test := do
  IO.FS.withTempDir fun dir => do
    let out := dir / "out.jsonl"
    result "shell" do
      IO.FS.writeFile out ""
      let r ← IO.Process.output
        { cmd := "bash", args := #[(harnessDir / "basic.sh").toString, "errata-run", out.toString, "no-such-test"] }
      assertTrue (r.exitCode != 0) "the exit code is not zero"
      assertNotContains "\"status\":\"pass\"" (← IO.FS.readFile out)
    result "Lean" do
      IO.FS.writeFile out ""
      let entry := TestEntry.of "p" "M" "exists" default (pure () : Test)
      let code ← Harness.dispatch #[entry] ["errata-run", out.toString, "no-such-test"]
      assertTrue (code != 0) "the exit code is not zero"
      assertNotContains "\"status\":\"pass\"" (← IO.FS.readFile out)

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
def eventsInDispatcherOrder : Test := do
  let r ← runWith #[basic ["records"]]
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
  assertTrue (strField ev[start]! "exe" == some "basic" &&
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

/--
A test that did not pass carries a command that reproduces it: its executable, {lit}`errata-run`, its
name, and its settings, quoted for a POSIX shell.
-/
@[test]
def reproductionLine : Test := do
  let r ← runWith #[basic ["fail", "pass"]] { sets := #[("note", "it's")] }
  let some res := r.result? "fail" | fail "no result"
  let some cmd := res.reproduce? | fail "no reproduction line"
  assertContains "basic.sh errata-run /dev/stderr fail setting:seed=" cmd
  assertContains "'setting:note=it'\\''s'" cmd
  assertNotContains "  " cmd
  result "a pass has none" do
    assertTrue ((r.result? "pass").bind (·.reproduce?)).isNone

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

/-- Durations are written with a unit. -/
@[test]
def durations : Test := do
  assertBEq (some 1000) (parseDuration "1s").toOption
  assertBEq (some 600000) (parseDuration "10m").toOption
  assertBEq (some 250) (parseDuration "250ms").toOption
  assertTrue (parseDuration "10" matches .error _)
  assertTrue (parseDuration "fast" matches .error _)

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
  let r ← runWith #[basic ["pass"]] { seed := some 7 }
  let some outcome := r.events.find? (isEvent "outcome") | fail "no outcome"
  assertBEq (some (toString (testSeed 7 "basic" "pass"))) (strField outcome "seed")
  assertBEq 7 r.report.seed

/--
A test whose mandatory setting has no value is inconclusive, naming the setting, and its process is
never started. The rest of the run goes on.
-/
@[test]
def settingMissing : Test := do
  let r ← runWith #[basic ["needs-setting", "pass"]]
  expectOutcome r "needs-setting" (· matches .inconclusive (.settingMissing "needed"))
    "settingMissing needed"
  let some res := r.result? "needs-setting" | fail "no result"
  assertNotContains "ran without its setting" res.output.all
  expectOutcome r "pass" (· matches .reported .pass) "a pass"
  result "a value from the command line lets it run" do
    let r ← runWith #[basic ["needs-setting"]] { sets := #[("needed", "yes")] }
    expectOutcome r "needs-setting" (· matches .reported .pass) "a pass"

/--
A value that the command line gives to a setting that no test executable declares stops the run
before anything runs, with the declared settings in the message. One that the profile gives is a
warning, since a profile serves every library's executable and a run may select some of them.
-/
@[test]
def undeclaredSettingRejected : Test := do
  result "on the command line" do
    let r ← runWith #[basic ["pass"]] { sets := #[("nonsense", "1")] }
    assertTrue r.report.results.isEmpty "no test ran"
    let some issue := r.report.issues.find? (·.isError) | fail "no error"
    assertContains "--set gives the setting nonsense a value, and no test executable of this run \
      declares it" issue.message
    assertContains "the declared settings are seed, marker, note, greeting, needed" issue.message
  result "in a profile" do
    let config : Config := { profiles := #[{ name := "default", settings := #[("other", "x")] }] }
    let r ← runWith #[basic ["pass"]] {} config
    expectOutcome r "pass" (· matches .reported .pass) "a pass"
    let some issue := r.report.issues.find? (!·.isError) | fail "no warning"
    assertContains "the profile default gives the setting other a value" issue.message
    let r ← runWith #[basic ["pass"]] { wfail := true } config
    assertTrue r.report.failsRun "--wfail makes it an error"

/--
A setting's declared default reaches a test that takes it, as an argument, when nothing else gives a
value. The test receives its settings in the order it takes them, and an optional setting without a
value is left out. `--list` shows the default and what the test receives.
-/
@[test]
def declaredDefaultReachesTest : Test := do
  let r ← runWith #[basic ["greets"]] { seed := some 7 }
  let some res := r.result? "greets" | fail "no result"
  let seed := toString (testSeed 7 "basic" "greets")
  assertBEq s!"received setting:seed={seed}\nreceived setting:greeting=hello\n" res.output.stdout
  assertBEq #[("seed", seed), ("greeting", "hello")] res.settings
  result "--list shows it" do
    let r ← runWith #[basic ["greets"]] { list := true, seed := some 7 }
    assertTrue (r.lines.contains "  greeting (default \"hello\")") s!"{r.lines}"
    assertTrue (r.lines.contains "        greeting = \"hello\"") s!"{r.lines}"
    assertTrue r.report.results.isEmpty "nothing ran"
  result "the command line wins over the default" do
    let r ← runWith #[basic ["greets"]] { sets := #[("greeting", "hi")] }
    let some res := r.result? "greets" | fail "no result"
    assertContains "received setting:greeting=hi\n" res.output.stdout

/-- An unknown profile stops the run, with the profiles in the message. -/
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
Once the inventory is known, a `tag(…)` that no test carries, an `exe(…)` that names no test
executable, and a filter that selects no test are warnings at their places, which `--wfail` makes
errors.
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
    let text : FilterText := { text := "name(pass) | tag(fast)", source := .file "errata.toml" 3 17 }
    let config : Config := { profiles := #[{ name := "default", defaultFilter? := some text }] }
    let r ← runWith #[basic ["pass"]] {} config
    assertBEq #["errata.toml:3:30: tag(fast) matches no tag of any test"]
      (r.report.issues.map (·.message))
  result "--wfail" do
    let r ← runWith #[basic ["pass"]] { filters := #["tag(fast) | name(pass)"], wfail := true }
    assertTrue r.report.failsRun

/-- An override's values apply to the tests its filter matches; the first match wins per value. -/
@[test]
def overridesApply : Test := do
  let overrides : Array Override := #[
    { filter := { text := "name(=greets)" }, settings := #[("greeting", "first")] },
    { filter := { text := "tag(shell)" }, settings := #[("greeting", "second"), ("note", "override")] }]
  let profile : Profile := { name := "default", settings := #[("note", "profile")], overrides }
  let config : Config := { profiles := #[profile] }
  let r ← runWith #[basic ["greets"]] {} config
  let some res := r.result? "greets" | fail "no result"
  assertContains "received setting:greeting=first\n" res.output.stdout
  assertContains "received setting:note=override\n" res.output.stdout

/--
Resolution takes each setting from the command line, then the first matching override that gives it,
then the profile, then the declared default, and for `seed` the derived seed; the timeout and grace
period from the command line, the first matching override, the profile, and the defaults; and the
slow mark and golden updating from the override, the profile, and the defaults.
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
    #[{ name := "x" }, { name := "y" }, { name := "z" }, { name := "w" }, { name := "seed" },
      { name := "v", optional := true }, { name := "u" }]
  let tagged : InventoryTest := { exeIdx := 0, name := "t", tags := #["a"], settings := deps }
  let plain : InventoryTest := { tagged with tags := #[] }
  let seed := toString (testSeed 3 "e" "t")
  result "the first matching override" do
    let r := ctx.resolve "e" declared tagged
    assertBEq #[("x", "first"), ("y", "second"), ("z", "profile"), ("w", "default"), ("seed", seed)]
      r.settings
    assertBEq #["u"] r.missing
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
      sets := #[("x", "cli"), ("seed", "12"), ("v", "given")], timeoutMs? := some 1
      gracePeriodMs? := some 2 }
    let r := ctx.resolve "e" declared tagged
    assertBEq (some "cli") ((r.settings.find? (·.1 == "x")).map (·.2))
    assertBEq (some "12") ((r.settings.find? (·.1 == "seed")).map (·.2))
    assertBEq (some "given") ((r.settings.find? (·.1 == "v")).map (·.2))
    assertBEq 1 r.timeoutMs
    assertBEq 2 r.gracePeriodMs
  result "the defaults" do
    let r := ({} : ResolutionContext).resolve "e" #[] { exeIdx := 0, name := "t" }
    assertBEq defaultTimeoutMs r.timeoutMs
    assertBEq defaultGracePeriodMs r.gracePeriodMs
    assertBEq defaultSlowAfterMs r.slowAfterMs
    assertBEq false r.updateGolden

/-- A test that runs longer than `slow-after` is marked slow in the human report, and its outcome stands. -/
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
def fastWriterTimesOut : Test := do
  let start ← IO.monoMsNow
  let r ← runWith #[basic ["flood"]] { timeoutMs? := some 1000, gracePeriodMs? := some 1000 }
  let wall := (← IO.monoMsNow) - start
  match r.outcome? "flood" with
  | some (.inconclusive (.timedOut ms _)) =>
    assertTrue (ms < 1000 + 1000 + 2000) s!"stopped only after {ms}ms"
  | o => fail s!"expected a timeout, got {repr o}"
  assertTrue (wall < 10000) s!"the run took {wall}ms"

/-- A second verdict record makes the result file unreadable, whatever the first one said. -/
@[test]
def twoVerdictsUnreadable : Test := do
  let r ← runWith #[basic ["twice"]]
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
    let config := dir / "config.json"
    let json := dir / "report.json"
    let exe : ExecutableConfig :=
      { name := "basic", command := #["bash", script.toString], env := #[("BASIC_TESTS", "lingers pass")] }
    IO.FS.writeFile config (Lean.toJson ({ executables := #[exe] } : Config)).compress
    let child ← IO.Process.spawn {
      cmd := runnerExe.toString
      args := #[config.toString, "--json", json.toString, "--grace-period", "500ms",
        "--set", s!"marker={marker}"]
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
  let exe : System.FilePath := ".lake/build/bin/errata-test-ErrataTests"
  unless ← exe.pathExists do fail s!"the test executable is not built at {exe}"
  IO.FS.withTempDir fun dir => do
    let out := dir / "out.jsonl"
    IO.FS.writeFile out ""
    let r ← IO.Process.output {
      cmd := exe.toString, args := #["errata-run", out.toString, "onePlusOne"]
      stdin := .null, env := #[("ERRATA_LIFELINE", none)]
    }
    assertExitCode 0 r
    assertContains "\"status\":\"pass\"" (← IO.FS.readFile out)

end ErrataTests.Conformance
