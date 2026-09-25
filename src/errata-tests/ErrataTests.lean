/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Tests that exercise Errata using Errata itself.
-/
module

public import Errata
public import Errata.WidgetRunner
public meta import Errata
import all Errata.FS
import ErrataTests.Fixture
import ErrataTests.Fixture.Sub
import ErrataTests.Docstrings
import ErrataTests.WidgetInteractive
import ErrataTests.Conformance
import ErrataTests.Settings
import ErrataTests.Roles
import ErrataTests.Filter

open Errata
open Errata.Widget.Runner

public section

/-- A bare boolean is a passing test. -/
@[test]
def onePlusOne : Bool := 1 + 1 == 2

/-- An assertion-based test. -/
@[test]
def equality : Test := do
  assertBEq 4 (2 + 2)

/-- A test with named results. -/
@[test]
def named : Test := do
  result "first" (assertBEq 1 1)
  result "second" (assertContains "b" "abc")

/-- A test that completes without any check is a bare success. -/
@[test]
def emptyBody : Test := pure ()

/-- An `unsafe` test is discovered and run like any other. -/
@[test]
unsafe def unsafeTest : Bool := true

/-- A test that expects a failure. -/
@[test]
def expectsFailure : Test :=
  expectFail (assertBEq 1 2)

/-- A data-driven family expressed as a plain loop. -/
@[test]
def squares : Test := do
  for (n, sq) in [(1, 1), (2, 4), (3, 9)] do
    result s!"square {n}" (assertBEq sq (n * n))

/-- A subprocess test. -/
@[test]
def echoRuns : Test := do
  let out ← IO.Process.output { cmd := "echo", args := #["hello"] }
  assertExitCode 0 out
  assertContains "hello" out.stdout

/-- info: 3 -/
#test_msgs in
#eval 1 + 2

-- The expected block is read from the source, so `#test_msgs` works in verso docstring mode.
set_option doc.verso true in
/-- info: 7 -/
#test_msgs in
#eval 3 + 4

/--
error: Module `NoSuchModule` is not imported, so its tests cannot be reached. Import it.
-/
#test_msgs in
example : Array TestEntry := getAllTests% "verso" NoSuchModule

/-- error: `onePlusOne` is already marked as a test -/
#test_msgs in
attribute [test] onePlusOne

/--
An exact module name leads to only its own tests being found. A name with a trailing `.*` also
contributes the tests of every module below it, and a module named more than once contributes its
tests once.
-/
@[test]
def discoveryNamesModules : Test := do
  result "exact" do
    assertBEq 1 (getAllTests% "verso" ErrataTests.Fixture).size
  result "below" do
    assertBEq 2 (getAllTests% "verso" ErrataTests.Fixture.*).size
  result "deduplicated" do
    -- `ErrataTests.Fixture.Sub` lies below the first name and is the second, so it is found once.
    assertBEq 2 (getAllTests% "verso" ErrataTests.Fixture.* ErrataTests.Fixture.Sub).size

/-- The docstring of a test in the docstring fixture module, when it has one. -/
private def fixtureDocstring (test : String) : Option String :=
  (getAllTests% "verso" ErrataTests.Docstrings).find? (·.name == test) |>.bind (·.docstring?)

/-- A test is named by its fully qualified declaration name, and its path is the name's components. -/
@[test]
def testsAreFullyQualified : Test := do
  let entries := getAllTests% "verso" ErrataTests.Docstrings
  let some entry := entries.find? (·.path.back? == some "customRoleDoc") | fail "the test is missing"
  assertBEq "ErrataTests.Docstrings.customRoleDoc" entry.name
  assertBEq #["ErrataTests", "Docstrings", "customRoleDoc"] entry.path

/-- error: `hidden` is private or not exported, so a test executable cannot reach it. Make it public, for example by declaring it in a `public section`. -/
#test_msgs in
@[test] private def hidden : Bool := true

/-- A Markdown docstring is captured as written. -/
@[test]
def markdownDocstringCaptured : Test := do
  let some doc := fixtureDocstring "markdownDoc" | assertTrue false "docstring missing"
  assertContains "with `code`, _emphasis_ and **strong** text." doc
  assertContains "* item one\n* item two" doc

/-- A Verso docstring is captured as Markdown: its roles become plain Markdown. -/
@[test]
def versoDocstringCaptured : Test := do
  let some doc := fixtureDocstring "versoDoc" | assertTrue false "docstring missing"
  assertContains "names `Nat.succ` and `x`, with *emphasis* and **strong** text." doc
  assertNotContains "{name}" doc
  assertNotContains "{lit}" doc
  assertContains "* item one" doc
  assertContains "* item two" doc

/--
A Verso role with its own Markdown renderer is rendered by it when the docstring is captured. The
renderer runs in the capturing scope, so the name it shortens comes out fully qualified.
-/
@[test]
def customRoleDocstringRendered : Test := do
  let some doc := fixtureDocstring "ErrataTests.Docstrings.customRoleDoc"
    | assertTrue false "docstring missing"
  assertContains "Refers to `ErrataTests.Docstrings.docstringTarget`, whose name" doc

/-- A test's docstring travels with its results. -/
@[test]
def docstringReachesResults : Test := do
  let cfg ← mkContext
  let results ← runEntry cfg <|
    TestEntry.of "p" "M" "documented" { file := "f", startPos := ⟨0, 0⟩, endPos := ⟨0, 0⟩ }
      (result "check" (assertBEq 1 2) : Test) (docstring? := some "What it checks.")
  result "the test's own result has it" do
    assertTrue (results.any fun r =>
      r.resultPath.isEmpty && r.description? == some "What it checks.")
  result "a named result has none" do
    assertTrue (results.any fun r => r.resultPath == #["check"] && r.description?.isNone)
  result "the Markdown report shows it once" do
    assertBEq 2 ((markdownReport { results, seed := 0 }).splitOn "What it checks.").length

/--
A result for the report tests: the test {name}`test` with the verdict {name}`v`, from an executable
with no name, so the human-readable report prints it without headings.
-/
private def sample (test : String) (v : Verdict) (resultPath : Array String := #[])
    (description? : Option String := none) (output : OutputLog := {}) (exe := "") : Result :=
  { exe, test, resultPath, outcome := .reported v, description?, output }

/--
The human-readable report shows a failure's docstring, indented below its status line, and shows a
pass's docstring only when every docstring is shown.
-/
@[test]
def reportShowsDocstring : Test := do
  let pass := sample "t" .pass (description? := some "Passing doc.")
  let fail := sample "u" (.fail { message := "boom" }) (description? := some "Failing doc.
Second line.")
  let silent ← captureOutput do discard <| humanReport .silent #[pass, fail]
  assertContains "FAIL  u: boom\n    Failing doc.\n    Second line.\n" silent.stdout
  assertNotContains "Passing doc." silent.stdout
  let verbose ← captureOutput do discard <| humanReport .verbose #[pass]
  assertNotContains "Passing doc." verbose.stdout
  let all ← captureOutput do discard <| humanReport .superVerbose #[pass]
  assertContains "ok    t" all.stdout
  assertContains "\n    Passing doc.\n" all.stdout

/--
The human-readable report nests tests below their executable and the levels of their paths, printing
each level once and each test by the last component of its path.
-/
@[test]
def reportNestsByPath : Test := do
  let at_ (path : Array String) : Result :=
    { exe := "Lib", test := ".".intercalate path.toList, path, outcome := .reported .pass }
  let out ← captureOutput do
    discard <| humanReport .verbose
      #[at_ #["A", "B", "one"], at_ #["A", "B", "two"], at_ #["A", "C", "three"], at_ #["four"]]
  let lines := out.stdout.splitOn "\n" |>.map fun l => (l.splitOn " (").headD l
  assertBEq ["Lib", "  A", "    B", "      ok    one", "      ok    two", "    C",
    "      ok    three", "  ok    four"] (lines.take 8)

/-- An inconclusive test is reported with its reason, its output, and the command that reproduces it. -/
@[test]
def reportShowsInconclusive : Test := do
  let r : Result := {
    test := "slow", outcome := .inconclusive (.timedOut 1000 false)
    output := { log := #[.stdout "partial\n"] }, reproduce? := some "exe errata-run out slow"
  }
  let out ← captureOutput do discard <| humanReport .silent #[r]
  assertContains "INCONCLUSIVE slow: timed out after 1000ms and was terminated" out.stdout
  assertContains "partial" out.stdout
  assertContains "reproduce: exe errata-run out slow" out.stdout
  assertContains "0 passed, 0 failed, 0 errors, 1 inconclusive" out.stdout
  let xml := junitReport { results := #[r], seed := 0 }
  assertContains "<error message=\"inconclusive: timed out after 1000ms and was terminated\" \
    type=\"timedOut\">" xml
  assertContains "**1** inconclusive" (markdownReport { results := #[r], seed := 0 })

/-- The Markdown report includes a failure's docstring as Markdown. -/
@[test]
def markdownReportShowsDocstring : Test := do
  let fail := sample "u" (.fail { message := "boom" }) (description? := some "Checks `x` and **y**.")
  assertContains "u: boom</summary>\n\nChecks `x` and **y**.\n\n"
    (markdownReport { results := #[fail], seed := 0 })

/-- A property test: a partial application of `property`, which takes the seed. -/
@[test]
def addComm : seed → Test :=
  property (∀ a b : Nat, a + b = b + a)

open Lean (toJson fromJson?)

deriving instance Plausible.Shrinkable, Plausible.Arbitrary for Lean.Position
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for Location
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for TestFailure
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for Verdict
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for FixturePhase
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for Inconclusive
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for Outcome
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for Output
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for OutputLog
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for Result.Kind
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for Result

/-- The JSON encoding of a result round-trips: decoding the encoding recovers the result. -/
@[test]
def jsonRoundTrips : seed → Test :=
  property (∀ r : Result, (fromJson? (toJson r)).toOption = some r)

/-- A temp-directory fixture with a golden file. -/
@[test]
def goldenRoundTrip : Test :=
  IO.FS.withTempDir fun dir => do
    let goldenPath := dir / "expected.txt"
    IO.FS.writeFile goldenPath "contents\n"
    assertFileExists goldenPath
    goldenFile goldenPath "contents\n"

/-- A golden file is written through directories that do not exist yet. -/
@[test]
def goldenFileCreatesDirectories : Test :=
  IO.FS.withTempDir fun dir =>
    withReader ({ · with updateGolden := true }) do
      let goldenPath := dir / "nested" / "deeper" / "expected.txt"
      goldenFile goldenPath "contents\n"
      assertFileExists goldenPath

/--
Runs one action as a test in a fresh context, returning the results it recorded. The test is given
a recognizable package, module, and source location, so a report that shows them is checked against
them.
-/
private def resultsOf (act : Test) : TestM (Array Result) := do
  let cfg ← mkContext
  runEntry cfg <|
    TestEntry.of "somePkg" "SomeFile" "inner"
      { file := "SomeFile.lean", startPos := ⟨42, 23⟩, endPos := ⟨42, 30⟩ } act

/-- A missing produced directory is a golden failure at the call site, not a bare error. -/
@[test]
def goldenDirReportsMissingOutput : Test := do
  let results ← IO.FS.withTempDir fun dir =>
    resultsOf (goldenDir (dir / "expected") (dir / "never-created"))
  assertBEq 1 results.size
  assertTrue (results[0]!.status matches .fail _)

/-- A produced directory with no files in it can be recorded and then compared. -/
@[test]
def goldenDirHandlesEmptyOutput : Test := do
  let results ← IO.FS.withTempDir fun dir => do
    let expected := dir / "expected"
    let actual := dir / "actual"
    IO.FS.createDirAll actual
    resultsOf do
      withReader ({ · with updateGolden := true }) (goldenDir expected actual)
      goldenDir expected actual
  assertBEq 1 results.size
  assertTrue results[0]!.status.isSuccess

/-- Updating absorbs a path that changed shape between file and directory, in both directions. -/
@[test]
def goldenDirUpdatesAcrossShapeChanges : Test := do
  let results ← IO.FS.withTempDir fun dir => do
    let expected := dir / "expected"
    let actual := dir / "actual"
    IO.FS.createDirAll expected
    IO.FS.writeFile (expected / "d") "was a file\n"
    IO.FS.createDirAll (actual / "d")
    IO.FS.writeFile (actual / "d" / "inner") "now a directory\n"
    resultsOf do
      -- First update: the golden file `d` becomes a directory holding `inner`.
      withReader ({ · with updateGolden := true }) (goldenDir expected actual)
      goldenDir expected actual
      -- Second update, the other way: the produced `d` is a file again.
      IO.FS.removeDirAll (actual / "d")
      IO.FS.writeFile (actual / "d") "a file once more\n"
      withReader ({ · with updateGolden := true }) (goldenDir expected actual)
      goldenDir expected actual
  assertBEq 1 results.size
  assertTrue results[0]!.status.isSuccess

/-- A file where a directory was expected is a golden failure, not a raw error. -/
@[test]
def goldenDirRejectsNonDirectory : Test := do
  let results ← IO.FS.withTempDir fun dir => do
    let actual := dir / "actual"
    IO.FS.writeFile actual "not a directory\n"
    resultsOf (goldenDir (dir / "expected") actual)
  assertBEq 1 results.size
  assertTrue (results[0]!.status matches .fail _)

/-- A directory standing where the golden tree has a file is a missing file, not a pass. -/
@[test]
def goldenDirRejectsDirectoryForFile : Test := do
  let results ← IO.FS.withTempDir fun dir => do
    let expected := dir / "expected"
    let actual := dir / "actual"
    writeFile (expected / "d") "contents\n"
    IO.FS.createDirAll (actual / "d")
    resultsOf (goldenDir expected actual)
  assertBEq 1 results.size
  assertTrue (results[0]!.status matches .fail _)

/-- A file standing where the golden tree has a directory is a golden failure, not a raw error. -/
@[test]
def goldenDirRejectsFileForDirectory : Test := do
  let results ← IO.FS.withTempDir fun dir => do
    let expected := dir / "expected"
    let actual := dir / "actual"
    writeFile (expected / "d" / "inner") "contents\n"
    writeFile (actual / "d") "not a directory\n"
    resultsOf (goldenDir expected actual)
  assertBEq 1 results.size
  assertTrue (results[0]!.status matches .fail _)

/-- Output written before a failure reaches the enclosing result, where it explains the failure. -/
@[test]
def captureOutputKeepsOutputOnFailure : Test := do
  let results ← resultsOf (discard <| captureOutput (do IO.println "diagnostic"; fail "boom"))
  assertBEq 1 results.size
  let r := results[0]!
  assertTrue (r.status matches .fail _)
  assertContains "diagnostic" r.output.all

/-- Output from an action that completes stays with the capture, rather than reaching the result. -/
@[test]
def captureOutputDivertsOnSuccess : Test := do
  let results ← resultsOf do
    let captured ← captureOutput (IO.println "quiet")
    assertContains "quiet" captured.all
  assertBEq 1 results.size
  assertTrue results[0]!.status.isSuccess
  assertTrue results[0]!.output.isEmpty

/-- A raw write may end partway through a code point; the write that completes it is joined on. -/
@[test]
def captureJoinsSplitWrites : Test := do
  let bytes := "é".toUTF8
  let captured ← captureOutput do
    let out ← IO.getStdout
    out.write (bytes.extract 0 1)
    out.write (bytes.extract 1 bytes.size)
  assertBEq "é" captured.stdout

/--
A write may end after a continuation byte of a wider code point. Its lead byte should stay behind
with it.
-/
@[test]
def captureJoinsSplitWideWrites : Test := do
  let bytes := "a😀".toUTF8
  let captured ← captureOutput do
    let out ← IO.getStdout
    out.write (bytes.extract 0 4)
    out.write (bytes.extract 4 bytes.size)
  assertBEq "a😀" captured.stdout

/-- Bytes whose code point is never completed are an error, not silently dropped. -/
@[test]
def captureRejectsDanglingBytes : Test := do
  let results ← resultsOf do
    let out ← IO.getStdout
    out.write ("é".toUTF8.extract 0 1)
  assertBEq 1 results.size
  assertTrue (results[0]!.status matches .error _)

/-- A test executable, written in shell, whose one test passes. -/
private def passingExe : Runner.ExecutableConfig :=
  ErrataTests.Conformance.basic ["pass"]

/--
Runs the runner on a configuration with every report written to a temporary directory, returning the
exit code and the JUnit, JSON, and Markdown reports.
-/
private def runReporting (config : Runner.Config) (args : List String) :
    TestM (UInt32 × String × String × String) :=
  IO.FS.withTempDir fun dir => do
    let xml := dir / "report.xml"
    let json := dir / "report.json"
    let md := dir / "report.md"
    let args := ["config.json", "--junit", xml.toString, "--json", json.toString,
      "--markdown", md.toString] ++ args
    let opts ← match Runner.parseOptions args with
      | .ok opts => pure opts
      | .error e => fail s!"the options do not parse: {e}"
    let code ← IO.mkRef (0 : UInt32)
    discard <| captureOutput do
      code.set (← Runner.executeAndWrite config opts)
    return (← code.get, ← IO.FS.readFile xml, ← IO.FS.readFile json, ← IO.FS.readFile md)

/--
The driver's warnings are warnings in every report, with the way to make them fail the run. Under
`--wfail` they are errors. A run with nothing to report has no "Test run" suite.
-/
@[test]
def warningsReachReports : Test := do
  let config : Runner.Config := { executables := #[passingExe] }
  let warned := { config with warnings := #["something looks off"] }
  result "absent without issues" do
    let (code, xml, _, _) ← runReporting config []
    assertBEq 0 code.toNat
    assertNotContains "Test run" xml
  result "as a warning" do
    let (code, xml, _, md) ← runReporting warned []
    assertBEq 0 code.toNat
    assertContains "<testsuite name=\"Test run\"" xml
    assertNotContains "<error" xml
    assertContains "something looks off" xml
    assertContains "--wfail" xml
    assertContains "something looks off" md
  result "as an error under --wfail" do
    let (code, xml, _, md) ← runReporting warned ["--wfail"]
    assertBEq 1 code.toNat
    assertContains "<error message=" xml
    assertContains "something looks off" xml
    assertContains "## ❌" md

/-- The run's seed reaches the JSON and Markdown reports. -/
@[test]
def seedReachesReports : Test := do
  let (_, _, json, md) ← runReporting { executables := #[passingExe] } ["--seed", "7"]
  let .ok j := Lean.Json.parse json | fail "the JSON report does not parse"
  assertBEq (some 7) (j.getObjValAs? Nat "seed").toOption
  assertContains "seed **7**" md

/-- A value from a wide range that is never shrunk, so that a counterexample reflects the seed. -/
structure Wide where
  n : Nat
deriving Repr

instance : Plausible.Shrinkable Wide where
  shrink _ := []

instance : Plausible.Arbitrary Wide where
  arbitrary := return ⟨← Plausible.Gen.choose Nat 0 (2 ^ 40) (by grind)⟩

/-- The detail of a result's failure, when it failed. -/
private def failDetail? (r : Result) : Option String :=
  match r.status with
  | .fail f => f.detail?
  | _ => none

/-- Runs a test that takes the seed with the given one, returning the seed and the results. -/
private def seededResults (seed : Nat) (act : Errata.seed → Test) : TestM (Nat × Array Result) := do
  let cfg ← mkContext
  return (seed, ← runEntry cfg (TestEntry.of "p" "M" "t" default (act seed)))

/--
A failed property's detail names the seed that produced its counterexample, and running again with
that seed produces the same counterexample. Another seed produces another counterexample.
-/
@[test]
def propertySeedReplays : Test := do
  let wide : Errata.seed → Test := property (∀ x : Wide, x.n ≠ x.n)
  let (seed, first) ← seededResults (← IO.rand 0 (2 ^ 32 - 1)) wide
  let some detail := failDetail? first[0]! | fail "expected the property to fail"
  -- The counterexample is the detail's first paragraph.
  let counterexample (detail : String) : String := (detail.splitOn "\n\n").headD detail
  result "the detail names the seed" do
    assertContains s!"seed {seed}" detail
  result "the seed replays the counterexample" do
    let (_, again) ← seededResults seed wide
    assertBEq (some (counterexample detail)) ((failDetail? again[0]!).map counterexample)
  result "another seed gives another counterexample" do
    let (_, other) ← seededResults (seed + 1) wide
    assertTrue (((failDetail? other[0]!).map counterexample) != some (counterexample detail))
      "the counterexample did not change with the seed"

/-- The detail given to a true-assertion is attached to its failure. -/
@[test]
def assertTrueAttachesDetail : Test := do
  let results ← resultsOf (assertTrue false "boom" (detail? := some "why"))
  assertBEq 1 results.size
  match results[0]!.status with
  | .fail f => assertBEq (some "why") f.detail?
  | s => fail s!"expected a failure, got {repr s}"

/-- An expected IO error passes, and the predicate picks which errors are acceptable. -/
@[test]
def assertThrowsIOAccepts : Test := do
  assertThrowsIO (throw (IO.userError "nope") : IO Unit)
  assertThrowsIO (throw (IO.userError "nope") : IO Unit)
    (acceptable := fun e => e matches .userError _)

/-- A successful action fails the throw assertion, as does an error the predicate rejects. -/
@[test]
def assertThrowsIORejects : Test := do
  expectFail (assertThrowsIO (pure () : IO Unit))
  expectFail <|
    assertThrowsIO (throw (IO.userError "nope") : IO Unit) (acceptable := fun _ => false)

/-- Output mixed from raw writes and prints is recorded in the order it was produced. -/
@[test]
def captureOrdersMixedWrites : Test := do
  let captured ← captureOutput do
    let out ← IO.getStdout
    out.write "é".toUTF8
    IO.print "x"
    out.write "û".toUTF8
  assertBEq "éxû" captured.stdout

/-- Text printed while a raw code point is unfinished is malformed output, not reordered output. -/
@[test]
def capturePrintDuringPartialWriteRejected : Test := do
  let results ← resultsOf do
    let out ← IO.getStdout
    out.write ("é".toUTF8.extract 0 1)
    IO.print "x"
  assertBEq 1 results.size
  assertTrue (results[0]!.status matches .error _)

/-- Dangling bytes at the end of a failing test do not displace the test's own failure. -/
@[test]
def danglingBytesKeepFailure : Test := do
  let results ← resultsOf do
    let out ← IO.getStdout
    out.write ("é".toUTF8.extract 0 1)
    fail "the real failure"
  assertBEq 1 results.size
  match results[0]!.status with
  | .fail f => assertBEq "the real failure" f.message
  | s => fail s!"expected the assertion failure, got {repr s}"

/-- A raw write with no valid decoding is rejected at the write itself. -/
@[test]
def captureRejectsInvalidBytes : Test := do
  let results ← resultsOf do
    let out ← IO.getStdout
    out.write (ByteArray.mk #[0xFF])
  assertBEq 1 results.size
  assertTrue (results[0]!.status matches .error _)

/--
A live output destination writes to the real stdout, so printing from it does not re-enter the
capture. The counter is bounded so that a regression fails this test instead of exhausting the stack.
-/
@[test]
def writeOutputDoesNotRecurse : Test := do
  let depth ← IO.mkRef 0
  let cfg ← mkContext
  let ctx := { cfg with
    writeOutput := some fun o => do
      depth.modify (· + 1)
      if (← depth.get) < 5 then
        match o with
        | .stdout s => IO.print s
        | .stderr s => IO.eprint s }
  discard <| runEntry ctx <|
    TestEntry.of "p" "M" "prints" { file := "f", startPos := ⟨0, 0⟩, endPos := ⟨0, 0⟩ }
      (IO.println "live" : Test)
  assertBEq 1 (← depth.get)

/--
A fragment printed inside a nested result reaches the live output destination exactly once. The
destination is cut off after a few fragments so that a regression fails this test with a short
array instead of flooding it.
-/
@[test]
def writeOutputDeliversNestedFragmentsOnce : Test := do
  let received ← IO.mkRef (#[] : Array String)
  let cfg ← mkContext
  let ctx := { cfg with
    writeOutput := some fun o => do
      if (← received.get).size < 5 then
        match o with
        | .stdout s => received.modify (·.push s); IO.print s
        | .stderr s => IO.eprint s }
  discard <| runEntry ctx <|
    TestEntry.of "p" "M" "nested" { file := "f", startPos := ⟨0, 0⟩, endPos := ⟨0, 0⟩ }
      (result "inner" (IO.println "hi") : Test)
  assertBEq #["hi\n"] (← received.get)

/--
A live output destination that fails does not fail the test that happened to be printing. It is
reported once and then left alone, rather than retried for every fragment.
-/
@[test]
def writeOutputFailureIsContained : Test := do
  let calls ← IO.mkRef 0
  let statuses ← IO.mkRef (#[] : Array Status)
  let cfg ← mkContext
  let ctx := { cfg with
    writeOutput := some fun _ => do
      calls.modify (· + 1)
      throw (.userError "broken pipe") }
  let out ← captureOutput do
    for name in ["first", "second"] do
      let entry := TestEntry.of "p" "M" name
        { file := "f", startPos := ⟨0, 0⟩, endPos := ⟨0, 0⟩ } (IO.println "output" : Test)
      for r in ← runEntry ctx entry do
        statuses.modify (·.push r.status)
  result "the printing tests are not blamed" do
    assertTrue ((← statuses.get).all (·.isSuccess))
  result "the destination is left alone after it fails" do
    assertBEq 1 (← calls.get)
  result "the failure is reported" do
    assertContains "live output destination failed" out.all

/-- A failure that a nested `result` recorded still satisfies `expectFail`. -/
@[test]
def expectFailSeesNestedResult : Test := do
  let results ← resultsOf (expectFail (result "inner" (assertBEq 1 2)))
  assertBEq 1 results.size
  assertTrue results[0]!.status.isSuccess

/-- An error inside `expectFail` is not an expected failure, even when a nested `result` records it. -/
@[test]
def expectFailRejectsNestedError : Test := do
  let results ← resultsOf <|
    expectFail (result "inner" (show IO Unit from throw (.userError "broken setup")))
  assertTrue (results.any (!·.status.isSuccess))

/--
An error two named results deep inside `expectFail` is recorded as an error, and so are the named
result above it and the test itself, since an error below a result makes it an error too.
`expectFail` keeps all three.
-/
@[test]
def expectFailRejectsDeeplyNestedError : Test := do
  let results ← resultsOf <| expectFail <|
    result "a" <| result "b" <| show IO Unit from throw (.userError "broken setup")
  assertBEq 3 results.size
  for path in [#[], #["a"], #["a", "b"]] do
    assertTrue (results.any fun r => r.resultPath == path && r.status matches .error _)
      s!"the result at {path} is an error"

/-- An error inside `expectFail` stands even when a sibling result recorded a failure. -/
@[test]
def expectFailKeepsErrorBesideFailure : Test := do
  let results ← resultsOf <| expectFail do
    result "a" <| assertBEq 1 2
    result "b" <| show IO Unit from throw (.userError "broken setup")
  assertTrue (results.any (·.status matches .error _))

/-- A nested failure satisfies `expectFail` whether or not the action goes on to throw. -/
@[test]
def expectFailAgreesAcrossPaths : Test := do
  let thrown ← resultsOf (expectFail (do result "a" (assertBEq 1 2); assertBEq 3 4))
  let recorded ← resultsOf (expectFail (do result "a" (assertBEq 1 2); result "b" (assertBEq 3 4)))
  result "action throws afterwards" (assertTrue (thrown.all (·.status.isSuccess)))
  result "action records only" (assertTrue (recorded.all (·.status.isSuccess)))

/-- Results other than the expected failure survive `expectFail`. -/
@[test]
def expectFailKeepsPassingResults : Test := do
  let results ← resultsOf <| expectFail do
    result "ok" (assertBEq 1 1)
    result "a" (assertBEq 1 2)
  assertTrue (results.any (fun r => r.status.isSuccess && r.testName.endsWith "ok"))

-- `here%` reports its own position, so the expected column below is the indentation of the line it
-- sits on, and the expected span is the five characters of the token itself.
def indentedHere : Location :=
  here%

/-- Source positions follow Lean's convention: lines count from one and columns from zero. -/
@[test]
def positionConvention : Test := do
  assertBEq 2 indentedHere.startPos.column
  assertBEq 5 (indentedHere.endPos.column - indentedHere.startPos.column)

/-- The `Verbosity` predicates behave as the report relies on. -/
@[test]
def verbosityLevels : Test := do
  assertBEq false Verbosity.silent.showsPasses
  assertBEq true Verbosity.quiet.showsPasses
  assertBEq true Verbosity.verbose.showsPasses
  assertBEq true Verbosity.superVerbose.showsPasses
  assertBEq false Verbosity.silent.truncates
  assertBEq true Verbosity.quiet.truncates
  assertBEq false Verbosity.verbose.truncates
  assertBEq false Verbosity.superVerbose.truncates
  assertBEq false Verbosity.verbose.showsAllDocstrings
  assertBEq true Verbosity.superVerbose.showsAllDocstrings

/-- The workspaces in which the self-tests run Verso's driver as a dependency's. -/
private def fixturesDir : System.FilePath := "src/errata-tests/fixtures"

/--
Runs Lake in a fixture workspace after deleting its manifest and packages directories.

The fixture requires Verso by path and shares its clones of dependencies. If Verso were updated,
then these could get out of date, leading to spurious rebuilds. Deleting them ensures that it always
uses the copies in Verso.
-/
private def lakeInFixture (fixture : System.FilePath) (args : Array String) :
    IO IO.Process.Output := do
  let manifest := fixture / "lake-manifest.json"
  if ← manifest.pathExists then IO.FS.removeFile manifest
  let packages := fixture / ".lake" / "packages"
  if ← packages.isDir then IO.FS.removeDirAll packages
  IO.Process.output { cmd := "lake", args, cwd := fixture }

/--
The driver tells users how it should be invoked, and works that out from the workspace it runs in.

The fixture workspaces under `fixtures` require Verso (and thus Errata) by path. `driver-bare`
neither names a test driver nor defines a script, so the command is a bare `lake run Errata.run`.
`driver-configured` names Verso's driver as its test driver, so the command is `lake test`.
`driver-shadowed` has an `Errata.run` script of its own that a bare name would run, so Verso's must
be named as `verso/Errata.run`.

The driver's help should show the expected command.
-/
@[test]
def driverHelpNamesInvocation : Test := do
  let cases : List (String × System.FilePath × String) := [
    ("bare", fixturesDir / "driver-bare", "lake run Errata.run"),
    ("configured", fixturesDir / "driver-configured", "lake test"),
    ("shadowed", fixturesDir / "driver-shadowed", "lake run verso/Errata.run")]
  for (name, fixture, run) in cases do
    result name do
      let out ← lakeInFixture fixture #["run", "verso/Errata.run", "--help"]
      assertExitCode 0 out
      assertContains s!"\n  {run} " out.stdout

/--
The driver runs `unsafe` tests. The fixture's `App` library has only safe tests, and its `AppUnsafe`
library has an unsafe one.
-/
@[test]
def driverRunsUnsafeTests : Test := do
  for (lib, passed) in [("App", 1), ("AppUnsafe", 2)] do
    result lib do
      let out ← lakeInFixture (fixturesDir / "driver-configured") #["test", "--", lib]
      assertExitCode 0 out
      assertContains s!"{passed} passed, 0 failed, 0 errors" out.stdout

/--
A module below a library's root that isn't imported transitively by any root causes a warning
because its tests are never discovered. The `--wfail` flag makes that report into an error. Either
way the tests run, and the reports record the warning or error. The fixture's `AppStray` library
has one such module.
-/
@[test]
def driverReportsUnreachableModules : Test := do
  let fixture := fixturesDir / "driver-configured"
  let notice := "modules are not reachable from their library's roots"
  IO.FS.withTempDir fun dir => do
    let junit := dir / "report.xml"
    let args := #["test", "--", "AppStray", "--test-options", "--junit", junit.toString]
    result "A warning is emitted" do
      let out ← lakeInFixture fixture args
      assertExitCode 0 out
      assertContains s!"warning: these {notice}" out.stderr
      assertContains "AppStray: AppStray.Orphan" out.stderr
      assertContains "1 passed, 0 failed, 0 errors" out.stdout
      let xml ← IO.FS.readFile junit
      assertContains "<testsuite name=\"Test run\"" xml
      assertContains "AppStray.Orphan" xml
      assertNotContains "<error" xml
    result "The --wfail flag turns the warning into an error" do
      let out ← lakeInFixture fixture (args.push "--wfail")
      assertExitCode 1 out
      assertContains s!"error: these {notice}" out.stderr
      assertContains "1 passed, 0 failed, 0 errors" out.stdout
      assertContains "<error message=" (← IO.FS.readFile junit)

/-- Indexes an empty array at the number of its arguments, and so panics. -/
@[test_helper]
def panicPlease (args : List String) : IO UInt32 := do
  let xs : Array Nat := #[]
  IO.println s!"{xs[args.length]!}"
  return 0

/--
A panic under `LEAN_ABORT_ON_PANIC=1` ends the process that panicked, after the runtime prints its
message on standard error. The helper indexes past the end of an array.
-/
@[test]
def arrayPanics : Test := do
  let out ← runHelper ``panicPlease ["one"] (env := #[("LEAN_ABORT_ON_PANIC", some "1")])
  assertAborted out
  assertContains "Error: index out of bounds" out.stderr

/--
Copies its standard input to its standard output, followed by the value of `ERRATA_HELPER_NOTE` on
a line of its own, and exits with the number of its arguments.
-/
@[test_helper]
def echoInput (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    IO.print line
  IO.println ((← IO.getEnv "ERRATA_HELPER_NOTE").getD "")
  return args.length.toUInt32

/--
A helper runs in a process of its own with the arguments, the environment, and the standard input
that the test gives it, and the test receives its exit code and output.
-/
@[test]
def helpersRunInTheirOwnProcess : Test := do
  let out ← runHelper ``echoInput ["a", "b", "c"] (env := #[("ERRATA_HELPER_NOTE", some "noted")])
    (stdin := "line one\nline two\n")
  assertExitCode 3 out
  assertBEq "line one\nline two\nnoted\n" out.stdout
  assertBEq "" out.stderr

/-- An `unsafe` helper that exits with 5. -/
@[test_helper]
unsafe def unsafeHelper (_ : List String) : IO UInt32 := pure 5

/-- An `unsafe` helper runs like any other. -/
@[test]
def unsafeHelperRuns : Test := do
  assertExitCode 5 (← runHelper ``unsafeHelper [])

/--
A name that matches no helper of the test executable ends the helper's process with exit code 2 and
a message that names it.
-/
@[test]
def unknownHelperIsReported : Test := do
  let out ← runHelper (Lean.Name.mkSimple "noSuchHelper") []
  assertExitCode 2 out
  assertContains "no helper is named noSuchHelper" out.stderr

/-- error: `hiddenHelper` is private or not exported, so a test executable cannot reach it. Make it public, for example by declaring it in a `public section`. -/
#test_msgs in
@[test_helper] private def hiddenHelper (_ : List String) : IO UInt32 := pure 0

/--
error: `@[test_helper]` requires the type `List String → IO UInt32`, and `wrongHelper` has the type
  Nat → IO UInt32
-/
#test_msgs in
@[test_helper] def wrongHelper (_ : Nat) : IO UInt32 := pure 0

/-- error: `panicPlease` is already marked as a test helper -/
#test_msgs in
attribute [test_helper] panicPlease

/-- error: A test helper must not be `meta` -/
#test_msgs in
@[test_helper] meta def metaHelper (_ : List String) : IO UInt32 := pure 0

/-- error: A test helper must not be `noncomputable` -/
#test_msgs in
@[test_helper] noncomputable def noncomputableHelper (_ : List String) : IO UInt32 :=
  pure (Classical.choice ⟨0⟩)

/-- error: A test helper must not be universe polymorphic -/
#test_msgs in
@[test_helper] def polymorphicHelper.{u} (_ : List String) : IO UInt32 :=
  pure (ULift.down.{u} (ULift.up 0))

/-- The type of a helper, under another name. -/
abbrev HelperFunction := List String → IO UInt32

-- A declaration whose type unfolds to the type of a helper is accepted.
#test_msgs in
@[test_helper] def abbreviatedHelper : HelperFunction := fun _ => pure 0

/-- Panics with `panic!`. -/
@[test_helper]
def panicExplicitly (_ : List String) : IO UInt32 :=
  panic! "on purpose"

/-- A panic from `panic!` prints a line that begins with `PANIC at` before the abort. -/
@[test]
def explicitPanics : Test := do
  let out ← runHelper ``panicExplicitly [] (env := #[("LEAN_ABORT_ON_PANIC", some "1")])
  assertAborted out
  assertContains "PANIC at" out.stderr
  assertContains "on purpose" out.stderr

/-- Writes a line to standard output and exits with 4, without reading its standard input. -/
@[test_helper]
def ignoresInput (_ : List String) : IO UInt32 := do
  IO.println "done"
  return 4

/--
A helper that exits without reading the standard input it is given still has its exit code and
output returned.
-/
@[test]
def unreadInputIsDropped : Test := do
  let out ← runHelper ``ignoresInput [] (stdin := "".pushn 'x' (1024 * 1024))
  assertExitCode 4 out
  assertBEq "done\n" out.stdout

/-- Writes the byte `0xFF`, which is not valid UTF-8, to standard output. -/
@[test_helper]
def writesInvalidUtf8 (_ : List String) : IO UInt32 := do
  (← IO.getStdout).write (ByteArray.mk #[0xFF])
  return 0

/-- Output that is not valid UTF-8 comes back with a replacement character for each invalid byte. -/
@[test]
def invalidOutputIsReplaced : Test := do
  let out ← runHelper ``writesInvalidUtf8 []
  assertExitCode 0 out
  assertBEq "�" out.stdout

/--
A test that panics ends its test executable's process, which the runner reports as ended by a
signal with the panic's message in its output, and the rest of the run goes on. The fixture's
`AppPanic` library has a test that indexes past the end of an array.
-/
@[test]
def driverReportsPanics : Test := do
  let out ← lakeInFixture (fixturesDir / "driver-configured") #["test", "--", "AppPanic"]
  assertExitCode 1 out
  assertContains "INCONCLUSIVE panics: the test executable was ended by signal 6" out.stdout
  assertContains "Error: index out of bounds" out.stdout
  assertContains "1 passed, 0 failed, 0 errors, 1 inconclusive" out.stdout

/--
A test executable runs the helpers that its tests start, including one from a module that has no
tests, and the inventory leaves helpers out. The fixture's `AppHelper` library has a test that runs a
helper from a module it imports.
-/
@[test]
def driverRunsHelpers : Test := do
  let fixture := fixturesDir / "driver-configured"
  result "The test runs its helper" do
    let out ← lakeInFixture fixture #["test", "--", "AppHelper"]
    assertExitCode 0 out
    assertContains "1 passed, 0 failed, 0 errors, 0 inconclusive" out.stdout
  result "The inventory has no helpers" do
    let out ← lakeInFixture fixture #["test", "--", "AppHelper", "--test-options", "--list"]
    assertExitCode 0 out
    assertContains "runsItsHelper" out.stdout
    assertNotContains "shout" out.stdout

/--
The `list` subcommand discovers the tests of every library and prints those that its filters select,
one per line with the executable, the name, the file and line, and the tags. A filter with a syntax
error is reported at its place, and the command fails.
-/
@[test]
def driverListsTests : Test := do
  let fixture := fixturesDir / "driver-configured"
  result "a filter" do
    let out ← lakeInFixture fixture #["test", "--", "list", "name(#*[Pp]anic*)"]
    assertExitCode 0 out
    let lines := out.stdout.splitOn "\n" |>.filter (·.startsWith "AppPanic")
    assertBEq 1 lines.length
    assertContains "panics" (lines.headD "")
    assertContains "AppPanic.lean:" (lines.headD "")
  result "several filters and none" do
    let two ← lakeInFixture fixture #["test", "--", "list", "exe(App)", "exe(AppUnsafe)"]
    assertExitCode 0 two
    assertBEq 3 (two.stdout.splitOn "\n" |>.filter (·.startsWith "App")).length
    let all ← lakeInFixture fixture #["test", "--", "list"]
    assertExitCode 0 all
    assertContains "safeTest" all.stdout
    assertContains "failsAsWritten" all.stdout
  result "a filter with a syntax error" do
    let out ← lakeInFixture fixture #["test", "--", "list", "name(x"]
    assertExitCode 1 out
    assertContains "list filter 1:6: expected ')' to end the matcher" out.stderr

/-- The workspace for the driver's tests of `errata.toml`, and the variants of the file it tries. -/
private def tomlFixture : System.FilePath := fixturesDir / "driver-toml"

/-- Copies a directory tree, leaving out Lake's build directory and manifest. -/
private partial def copyTree (src dst : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  for entry in ← src.readDir do
    if entry.fileName == ".lake" || entry.fileName == "lake-manifest.json" then continue
    if ← entry.path.isDir then copyTree entry.path (dst / entry.fileName)
    else IO.FS.writeBinFile (dst / entry.fileName) (← IO.FS.readBinFile entry.path)

/--
Copies a fixture workspace into {name}`dir`, so that a test changes and builds its own copy. The
lakefile's relative paths to Verso and to Verso's packages become absolute, so the copy builds
wherever it is.
-/
private def copyFixture (fixture dir : System.FilePath) : IO Unit := do
  let root ← IO.FS.realPath "."
  copyTree fixture dir
  for name in ["lakefile.lean", "lakefile.toml"] do
    let file := dir / name
    if ← file.pathExists then
      let text ← IO.FS.readFile file
      -- The packages' path begins with Verso's, so it is replaced first.
      let text := text.replace "\"../../../../.lake/packages\"" (root / ".lake" / "packages").toString.quote
        |>.replace "\"../../../..\"" root.toString.quote
      IO.FS.writeFile file text

/--
Runs Lake with {name}`args` in a copy of the `driver-toml` fixture whose `errata.toml` is the variant
{name}`name`.
-/
private def withTomlVariant (name : String) (args : Array String) : IO IO.Process.Output :=
  IO.FS.withTempDir fun dir => do
    copyFixture tomlFixture dir
    IO.FS.writeFile (dir / "errata.toml") (← IO.FS.readFile (tomlFixture / "variants" / s!"{name}.toml"))
    IO.Process.output { cmd := "lake", args, cwd := dir }

/--
The driver checks `errata.toml` before it builds any test executable, and reports each problem at
its position in the file: a TOML syntax error, a setting that is neither a string nor
`{ needs = … }` whether its name is a quoted key or nested tables, an unknown key, profiles that
inherit in a cycle, a malformed duration, an unknown target, and a malformed `[[executable]]`.
-/
@[test]
def driverValidatesToml : Test := do
  let cases : List (String × List String) := [
    ("syntax", ["errata.toml:1:16:"]),
    ("wrong-type", ["errata.toml:2:22: the setting 'TomlLib.stampFile' must be a string or \
      { needs = \"target\" }, and it is an integer"]),
    ("nested-wrong-type", ["errata.toml:2:20: the setting 'TomlLib.stampFile' must be a string or \
      { needs = \"target\" }, and it is a boolean"]),
    ("unknown-key", ["errata.toml:3:9: unknown key 'flavor' in the profile 'default'"]),
    ("cycle", ["errata.toml:2:11: the profiles inherit in a cycle: a → b → a",
      "errata.toml:5:11: the profiles inherit in a cycle: b → a → b"]),
    ("bad-duration", ["errata.toml:2:10: 'timeout' must be a duration"]),
    ("unknown-target", ["errata.toml:2:32: the target 'nonexistent' cannot be built:"]),
    ("bad-executable", ["errata.toml:3:10: 'command' must have at least one word"])]
  for (variant, messages) in cases do
    result variant do
      let out ← withTomlVariant variant #["test"]
      assertExitCode 1 out
      for m in messages do
        assertContains m out.stderr
      assertNotContains "errataExe" out.stdout

/--
A setting's name may be written as nested tables as well as a quoted dotted key, and the driver
reads a file that begins with a byte-order mark and durations with spaces around them. A filter in a
multi-line string is reported at its line and column in the file.
-/
@[test]
def driverReadsTomlForms : Test := do
  result "nested tables, a byte-order mark, and a duration with spaces" do
    for variant in ["nested", "bom"] do
      let out ← withTomlVariant variant #["test"]
      assertExitCode 0 out
      assertContains "1 passed, 0 failed, 0 errors, 0 inconclusive" out.stdout
  result "a multi-line filter" do
    let out ← withTomlVariant "multiline-filter" #["test"]
    assertExitCode 1 out
    assertContains "errata.toml:4:8: expected ')' to end the matcher" out.stderr

/--
A setting bound to a target with `{ needs = … }` receives the target's result. Editing the target's
input rebuilds the runner's configuration, and leaves the test library alone.
-/
@[test]
def driverBuildsNeededTargets : Test :=
  IO.FS.withTempDir fun dir => do
    copyFixture tomlFixture dir
    let lake (args : Array String) : IO IO.Process.Output :=
      IO.Process.output { cmd := "lake", args, cwd := dir }
    let config := dir / ".lake" / "errata" / "config.json"
    let olean := dir / ".lake" / "build" / "lib" / "lean" / "TomlLib.olean"
    let out ← lake #["test"]
    assertExitCode 0 out
    assertContains "1 passed, 0 failed, 0 errors, 0 inconclusive" out.stdout
    assertContains "stamp.txt" (← IO.FS.readFile config)
    let configBefore := (← config.metadata).modified
    let oleanBefore := (← olean.metadata).modified
    IO.FS.writeFile (dir / "stamp-input.txt") "stamp 2\n"
    let again ← lake #["test"]
    assertExitCode 0 again
    result "the configuration is rebuilt" do
      assertTrue ((← config.metadata).modified != configBefore) "config.json was not rewritten"
    result "the test library is not" do
      assertTrue ((← olean.metadata).modified == oleanBefore) "TomlLib.olean was rebuilt"

/--
The driver builds only the targets that the selected profile's settings need. A name on the command
line selects a test executable that `errata.toml` adds, as it selects a library, and such an
executable receives the directory of Errata's sources. The runner's configuration says when the
command line named what to test, and a name that matches nothing is an error that names both kinds.
-/
@[test]
def driverSelectsProfilesAndExecutables : Test :=
  IO.FS.withTempDir fun dir => do
    copyFixture tomlFixture dir
    IO.FS.writeFile (dir / "errata.toml")
      (← IO.FS.readFile (tomlFixture / "variants" / "profile-needs.toml"))
    let lake (args : Array String) : IO IO.Process.Output :=
      IO.Process.output { cmd := "lake", args, cwd := dir }
    let stamp := dir / ".lake" / "build" / "stamp.txt"
    let config : TestM Lean.Json := do
      match Lean.Json.parse (← IO.FS.readFile (dir / ".lake" / "errata" / "config.json")) with
      | .ok j => pure j
      | .error e => fail s!"config.json is not JSON: {e}"
    let exeNames (j : Lean.Json) : Array String :=
      ((j.getObjValAs? (Array Lean.Json) "executables").toOption.getD #[]).filterMap fun e =>
        (e.getObjValAs? String "name").toOption
    result "an added executable alone, with the default profile" do
      let out ← lake #["test", "--", "extra"]
      assertExitCode 0 out
      assertContains "1 passed, 0 failed" out.stdout
      assertTrue (!(← stamp.pathExists)) "the default profile needs no target, and the stamp was built"
      let j ← config
      assertBEq #["extra"] (exeNames j)
      assertBEq (some (← IO.FS.realPath "src/errata").toString)
        (j.getObjValAs? String "errataDir").toOption
      assertBEq (some true) (j.getObjValAs? Bool "partial-selection").toOption
    result "a library alone" do
      discard <| lake #["test", "--", "TomlLib"]
      assertBEq #["TomlLib"] (exeNames (← config))
    result "the profile that needs the stamp" do
      let out ← lake #["test", "--", "--test-options", "--profile", "stamped"]
      assertExitCode 0 out
      assertContains "2 passed, 0 failed" out.stdout
      assertTrue (← stamp.pathExists) "the stamp was not built"
      let j ← config
      assertBEq #["TomlLib", "extra"] (exeNames j)
      assertBEq none (j.getObjValAs? Bool "partial-selection").toOption
    result "an unknown name" do
      let out ← lake #["test", "--", "Nothing"]
      assertExitCode 1 out
      assertContains "no library, and no [[executable]] in errata.toml, matches 'Nothing'" out.stderr

/-- The `list` subcommand takes filters only, and an option given to it is an error. -/
@[test]
def listRejectsOptions : Test := do
  for opt in ["--profile", "--set", "--test-options", "-v"] do
    result opt do
      let out ← withTomlVariant "nested" #["test", "--", "list", "tag(x)", opt]
      assertExitCode 1 out
      assertContains s!"the `list` subcommand takes filters only, and {opt} is an option" out.stderr

/--
The compile-time commands register their verdicts as tests, so a module that imports only
`Errata.CompileTime` builds and its tests are discovered. The fixture's `AppCompileTime` library has
one `#test_guard` and one `#test_msgs`.
-/
@[test]
def compileTimeImportSuffices : Test := do
  let out ← lakeInFixture (fixturesDir / "driver-configured") #["test", "--", "AppCompileTime"]
  assertExitCode 0 out
  assertContains "2 passed, 0 failed, 0 errors" out.stdout

/--
A test in a dependency's library runs in that library's own test executable, which is built in the
dependency's build directory. The fixture requires the `dep` package, whose `DepLib` library has one
test.
-/
@[test]
def dependencyTestsHaveTheirOwnExecutable : Test := do
  let fixture := fixturesDir / "driver-configured"
  IO.FS.withTempDir fun dir => do
    let junit := dir / "report.xml"
    let out ← lakeInFixture fixture
      #["test", "--", "dep/DepLib", "--test-options", "-v", "--junit", junit.toString]
    assertExitCode 0 out
    assertContains "DepLib\n  ok    depTest" out.stdout
    assertContains "<testsuite name=\"DepLib\"" (← IO.FS.readFile junit)
    let config ← IO.FS.readFile (fixture / ".lake" / "errata" / "config.json")
    assertContains "dep/.lake/build/bin/errata-test-DepLib" config

/--
A root without a `module` header that imports a module-system child, each with a test, has each
test discovered once.
The fixture's `AppMixed` library has that shape.
-/
@[test]
def mixedDiscoveryRunsEachTestOnce : Test := do
  let out ← lakeInFixture (fixturesDir / "driver-configured")
    #["test", "--", "AppMixed", "--test-options", "-v"]
  assertExitCode 0 out
  assertContains "ok    parentTest" out.stdout
  assertContains "ok    childTest" out.stdout
  assertBEq 2 (out.stdout.splitOn "childTest").length
  assertContains "2 passed, 0 failed, 0 errors" out.stdout

/--
A test that runs past the timeout is reported as timed out, and the run goes on. What a test's
subprocess writes reaches the report. The fixture's `AppSlow` library has a test that sleeps and one
that prints from a subprocess.
-/
@[test]
def driverEnforcesTimeouts : Test := do
  let fixture := fixturesDir / "driver-configured"
  IO.FS.withTempDir fun dir => do
    let junit := dir / "report.xml"
    let out ← lakeInFixture fixture
      #["test", "--", "AppSlow", "--test-options", "--timeout", "1s", "--junit", junit.toString]
    assertExitCode 1 out
    assertContains "INCONCLUSIVE sleeps: timed out after" out.stdout
    assertContains "1 passed, 0 failed, 0 errors, 1 inconclusive" out.stdout
    let xml ← IO.FS.readFile junit
    assertContains "type=\"timedOut\"" xml
    assertContains "from a subprocess" xml

/--
The `IsTest` instance that runs a test is the one in force where the test is declared. The
fixture's `AppLocalInstance` library has a test whose type has only a local instance, and its
`AppShadow` library has a failing boolean test beside a module whose high-priority instance would
pass it.
-/
@[test]
def instanceIsFixedAtDeclaration : Test := do
  let fixture := fixturesDir / "driver-configured"
  result "a local instance runs the test" do
    let out ← lakeInFixture fixture #["test", "--", "AppLocalInstance"]
    assertExitCode 0 out
    assertContains "1 passed, 0 failed, 0 errors" out.stdout
  result "an instance elsewhere does not change the verdict" do
    let out ← lakeInFixture fixture #["test", "--", "AppShadow"]
    assertExitCode 1 out
    assertContains "FAIL  failsAsWritten" out.stdout
    assertContains "1 passed, 1 failed, 0 errors" out.stdout

/-- A test that prints, then records a named result that sleeps and fails. -/
private def setupThenFailingCheck : Test := do
  IO.println "setup"
  result "check" do
    IO.sleep 30
    assertContains "hello" "goodbye"

/--
A test that records named results contributes a result of its own, before them. Its report includes
the output written outside the named results and the time spent outside them, and it fails when one
of them did not pass.
-/
@[test]
def testKeepsOwnOutputAndTime : Test := do
  let results ← resultsOf setupThenFailingCheck
  let some own := results.find? (·.resultPath.isEmpty) | fail "the test's own result is missing"
  assertBEq "setup\n" own.output.stdout
  let .fail f := own.status
    | fail s!"expected the test to fail with its named result, got {repr own.status}"
  assertBEq "a named result did not pass" f.message
  let some check := results.find? (·.resultPath == #["check"]) | fail "the named result is missing"
  assertTrue (30 ≤ check.durationMs) "the named result's time includes its sleep"
  assertTrue (own.durationMs < check.durationMs) "the test's own time leaves out its named result's"
  assertBEq (some own) results[0]?

/--
The human-readable report shows a test's own failure, with the test's output, above the named
result that made it fail, and counts both.
-/
@[test]
def reportShowsTestOutputAboveFailedNamedResult : Test := do
  let results ← resultsOf setupThenFailingCheck
  let failures ← IO.mkRef 0
  let out ← captureOutput do failures.set (← humanReport .silent results)
  let own := "FAIL  inner: a named result did not pass\n" ++
    "    SomeFile.lean:42:23\n    output:\n    setup\n"
  assertContains own out.stdout
  -- The named result follows the test's own result.
  assertTrue (((out.stdout.splitOn own)[1]?.getD "").startsWith "  FAIL  check: ")
    "the named result's line follows the test's output"
  assertContains "0 passed, 2 failed, 0 errors, 0 inconclusive" out.stdout
  assertBEq 2 (← failures.get)

/-- Named results print indented under their test by their own names, siblings included. -/
@[test]
def reportIndentsNamedResultsUnderTheirParent : Test := do
  let results ← resultsOf do
    result "b" (pure ())
    result "c" (result "d" (pure ()))
  let out ← captureOutput do discard <| humanReport .verbose results
  assertTrue (out.stdout.startsWith "ok    inner (")
    "the test's own line comes first"
  assertContains "\n  ok    b (" out.stdout
  assertContains "\n  ok    c (" out.stdout
  assertContains "\n    ok    d (" out.stdout

/--
The time of a named result that `expectFail` drops is still the named result's own, so the test's
duration leaves it out.
-/
@[test]
def expectFailKeepsDroppedTimeOutOfOwnDuration : Test := do
  let results ← resultsOf <| expectFail <| result "slow" do
    IO.sleep 50
    assertBEq 1 2
  assertBEq 1 results.size
  let own := results[0]!.durationMs
  assertTrue (own < 50) s!"the test's own duration, {own}ms, includes the dropped named result's"

/-- The JUnit report has a case for the test and for its named result, each with its own output. -/
@[test]
def junitIncludesTestOutputOnFailedNamedResult : Test := do
  let results ← resultsOf setupThenFailingCheck
  let xml := junitReport { results, seed := 0 }
  assertContains "tests=\"2\" failures=\"2\"" xml
  assertContains "<system-out>setup" xml
  assertBEq 1 ((xml.splitOn "<system-out>").length - 1)

/-- The runner's help names the command that its options follow, which the configuration records. -/
@[test]
def runnerHelpNamesInvocation : Test := do
  IO.FS.withTempDir fun dir => do
    let config := dir / "config.json"
    let invocation := "lake test -- --test-options"
    IO.FS.writeFile config (Lean.toJson ({ invocation? := some invocation } : Runner.Config)).compress
    let out ← captureOutput do
      discard <| Runner.main [config.toString, "--help"]
    assertContains s!"{invocation} [FLAGS]" out.all

/--
The runner's command line: the configuration file first, the `-v` forms select the verbosity,
declared flags parse, `--set` and `--filter` repeat, and `list` begins the subcommand.
-/
@[test]
def runnerArgParsing : Test := do
  let parse (args : List String) := Runner.parseOptions ("config.json" :: args)
  result "configuration" do
    assertBEq (some "config.json") ((parse []).toOption.map (·.configPath))
  result "default verbosity" do
    assertBEq (some Verbosity.silent) ((parse []).toOption.map (·.verbosity))
  result "-v" do
    assertBEq (some Verbosity.quiet) ((parse ["-v"]).toOption.map (·.verbosity))
  result "--verbose" do
    assertBEq (some Verbosity.quiet) ((parse ["--verbose"]).toOption.map (·.verbosity))
  result "-vv" do
    assertBEq (some Verbosity.verbose) ((parse ["-vv"]).toOption.map (·.verbosity))
  result "-vvv" do
    assertBEq (some Verbosity.superVerbose) ((parse ["-vvv"]).toOption.map (·.verbosity))
  result "update-golden" do
    assertBEq (some true) ((parse ["--update-golden"]).toOption.map (·.updateGolden))
  result "seed" do
    assertBEq (some (some 42)) ((parse ["--seed", "42"]).toOption.map (·.seed))
  result "non-numeric seed rejected" do
    assertTrue ((parse ["--seed", "x"]) matches .error _)
  result "junit path" do
    assertBEq (some (some "r.xml")) ((parse ["--junit", "r.xml"]).toOption.map (·.junitPath))
  result "missing junit path rejected" do
    assertTrue ((parse ["--junit"]) matches .error _)
  result "events path" do
    assertBEq (some (some "e.jsonl")) ((parse ["--events", "e.jsonl"]).toOption.map (·.eventsPath))
  result "list" do
    assertBEq (some true) ((parse ["--list"]).toOption.map (·.list))
  result "timeout and grace period" do
    let opts := (parse ["--timeout", "90s", "--grace-period", "250ms"]).toOption
    assertBEq (some (some 90000)) (opts.map (·.timeoutMs?))
    assertBEq (some (some 250)) (opts.map (·.gracePeriodMs?))
  result "hours" do
    assertBEq (some (some 7200000)) ((parse ["--timeout", "2h"]).toOption.map (·.timeoutMs?))
  result "no timeout given" do
    assertBEq (some none) ((parse []).toOption.map (·.timeoutMs?))
  result "malformed timeout rejected" do
    assertTrue ((parse ["--timeout", "soon"]) matches .error _)
  result "one job" do
    assertBEq (some 1) ((parse ["--jobs", "1"]).toOption.map (·.jobs))
  result "more jobs rejected" do
    assertTrue ((parse ["--jobs", "2"]) matches .error _)
  result "no jobs rejected" do
    assertTrue ((parse ["--jobs", "0"]) matches .error _)
  result "zero timeout rejected" do
    assertTrue ((parse ["--timeout", "0s"]) matches .error _)
  result "settings" do
    let opts := (parse ["--set", "golden=on", "--set=flag=v=1", "-v", "--set", "empty="]).toOption
    assertBEq (some #[("golden", "on"), ("flag", "v=1"), ("empty", "")]) (opts.map (·.sets))
    assertBEq (some Verbosity.quiet) (opts.map (·.verbosity))
  result "a setting without = rejected" do
    assertTrue ((parse ["--set", "golden"]) matches .error _)
  result "a setting without a value rejected" do
    assertTrue ((parse ["--set"]) matches .error _)
  result "profile" do
    assertBEq (some "default") ((parse []).toOption.map (·.profile))
    assertBEq (some "ci") ((parse ["--profile", "ci"]).toOption.map (·.profile))
  result "filters" do
    let opts := (parse ["--filter", "name(a)", "--filter=tag(slow)"]).toOption
    assertBEq (some #["name(a)", "tag(slow)"]) (opts.map (·.filters))
  result "the list subcommand" do
    let opts := (parse ["list", "name(a)", "exe(B)"]).toOption
    assertBEq (some (some #["name(a)", "exe(B)"])) (opts.map (·.listFilters?))
    assertBEq (some none) ((parse []).toOption.map (·.listFilters?))
  result "the list subcommand with an option" do
    for opts in [["--profile", "ci"], ["--set", "a=b"], ["--filter", "tag(x)"], ["-v"]] do
      match parse (["list", "tag(x)"] ++ opts) with
      | .error m => assertContains "the `list` subcommand takes filters only" m
      | .ok _ => fail s!"{opts} was accepted"
  result "options after -- rejected" do
    assertTrue ((parse ["--", "--golden", "on"]) matches .error _)
  result "unknown flag rejected" do
    assertTrue ((parse ["--golden", "on"]) matches .error _)
  result "panic flags rejected" do
    assertTrue ((parse ["--ignore-panics"]) matches .error _)
    assertTrue ((parse ["--exit-on-panic"]) matches .error _)
  result "misplaced library name diagnosed" do
    match parse ["--verbose", "ErrataTests"] with
    | .error msg => assertContains "ErrataTests" msg
    | .ok _ => assertTrue false "expected an error"

/--
The Lean harness reads the settings among its arguments, reads its own `updateGolden`, and reaches
helpers through its own executable.
-/
@[test]
def harnessSettings : Test := do
  let settings := Harness.settingsOf
    ["setting:seed=5", "setting:check-tex=", "setting:note=a=b", "fixture:x=y", "threads:2"]
  assertBEq #[("seed", "5"), ("check-tex", ""), ("note", "a=b")] settings
  let ctx ← Harness.contextOf settings
  assertBEq false ctx.updateGolden
  assertTrue (← Harness.contextOf #[("updateGolden", "true")]).updateGolden
  assertBEq (some "errata-helper") (ctx.helperCommand.bind (·[1]?))
  assertTrue ctx.legacyOptions?.isNone "a test executable passes no free-form options"

/--
The Lean harness lists its tests with their names, paths, and locations, runs one by name, writing
its records and exiting with its verdict, and runs a helper by name, exiting with its exit code.
-/
@[test]
def harnessListsAndRuns : Test := do
  let loc : Location := { file := "F.lean", startPos := ⟨3, 0⟩, endPos := ⟨4, 0⟩ }
  let entries := #[
    TestEntry.of "p" "M" "M.good" loc (do IO.println "hello"; result "inner" (pure ()) : Test)
      (docstring? := some "Good."),
    TestEntry.of "p" "M" "M.bad" loc (fail "nope" : Test)]
  -- The records of a list file or a result file, decoded.
  let records (path : System.FilePath) : TestM (Array Protocol.Record) := do
    let lines := (← IO.FS.readFile path).splitOn "\n" |>.filter (!·.isEmpty)
    let mut out := #[]
    for l in lines do
      match Protocol.Record.parseLine l with
      | .ok (some (_, r)) => out := out.push r
      | .ok none => fail s!"a record of an unknown type: {l}"
      | .error e => fail s!"a line that is not a record: {e}"
    return out
  IO.FS.withTempDir fun dir => do
    let out := dir / "out.jsonl"
    result "list" do
      IO.FS.writeFile out ""
      assertBEq 0 (← Harness.dispatch entries ["errata-list", out.toString])
      let rs : Array Protocol.Record ← records out
      assertTrue (rs[0]? matches some (Protocol.Record.protocol (some 1))) "the protocol comes first"
      let some (Protocol.Record.test info) := rs[1]? | fail "the first test is missing"
      assertBEq (some "M.good") info.name?
      assertBEq (some #["M", "good"]) info.path?
      assertBEq (some "F.lean") info.file?
      assertBEq (some 3) info.line?
      assertBEq (some "Good.") info.description?
      assertBEq 3 rs.size
    result "a pass" do
      IO.FS.writeFile out ""
      assertBEq 0 (← Harness.dispatch entries ["errata-run", out.toString, "M.good"])
      let rs ← records out
      assertTrue (rs.any (· matches .start _)) "a start record"
      assertTrue (rs.any (· matches .output (some "stdout") (some "hello\n") _ (some 0)))
        "the output record"
      assertTrue (rs.any fun
        | .result i => i.id? == some 1 && i.name? == some "inner" && i.status?.isNone
        | _ => false) "the named result's start"
      assertTrue (rs.back? matches some (.verdict { status? := some .pass, .. })) "the verdict comes last"
    result "a failure" do
      IO.FS.writeFile out ""
      assertBEq 1 (← Harness.dispatch entries ["errata-run", out.toString, "M.bad"])
      let rs ← records out
      assertTrue (rs.back? matches some (.verdict { status? := some .fail, message? := some "nope", .. }))
        "a failing verdict"
    result "usage" do
      let code ← IO.mkRef (0 : UInt32)
      let printed ← captureOutput do code.set (← Harness.dispatch entries [])
      assertBEq 2 (← code.get)
      assertContains "errata-list" printed.stderr
      assertContains "errata-helper" printed.stderr
    let helpers : Array Helper := #[{ name := "M.count", run := fun args => pure args.length.toUInt32 }]
    result "a helper" do
      assertBEq 2 (← Harness.dispatch entries ["errata-helper", "M.count", "x", "y"] helpers)
    result "an unknown helper" do
      let code ← IO.mkRef (0 : UInt32)
      let printed ← captureOutput do
        code.set (← Harness.dispatch entries ["errata-helper", "M.other"] helpers)
      assertBEq 2 (← code.get)
      assertContains "no helper is named M.other" printed.stderr

/-- A run that discovers nothing fails: a test tool with no tests is a broken setup, not a pass. -/
@[test]
def emptyRunFails : Test := do
  let code ← IO.mkRef (0 : UInt32)
  let out ← captureOutput do
    code.set (← Runner.executeAndWrite {} {})
  assertContains "no tests were discovered" out.all
  assertBEq 1 (← code.get).toNat

/--
Every report records a run that discovered nothing as a failed run: JUnit has a "Test run" suite
with an error case, the JSON object lists the issue, and the Markdown headline is red.
-/
@[test]
def emptyRunReachesReports : Test := do
  let (code, xml, json, md) ← runReporting {} []
  assertBEq 1 code.toNat
  result "JUnit" do
    assertContains "<testsuite name=\"Test run\"" xml
    assertContains "<error message=\"no tests were discovered\"" xml
  result "JSON" do
    let .ok j := Lean.Json.parse json | fail "the JSON report does not parse"
    let .ok issues := j.getObjValAs? (Array Lean.Json) "issues" | fail "no issues field"
    assertBEq 1 issues.size
    assertBEq (some "error") (issues[0]!.getObjValAs? String "level").toOption
    assertContains "no tests were discovered" ((issues[0]!.getObjValAs? String "message").toOption.getD "")
  result "Markdown" do
    assertContains "## ❌" md
    assertContains "no tests were discovered" md

/-- At silent verbosity the report hides passes but shows failures and the summary line. -/
@[test]
def reportSilent : Test := do
  let pass := sample "t" .pass
  let fail := sample "u" (.fail { message := "boom" })
  let out ← captureOutput do discard <| humanReport .silent #[pass, fail]
  assertContains "FAIL  u: boom" out.stdout
  assertContains "1 passed, 1 failed, 0 errors, 0 inconclusive" out.stdout
  assertBEq 1 (out.stdout.splitOn "ok    ").length

/-- At verbose verbosity the report shows passes too. -/
@[test]
def reportVerbose : Test := do
  let out ← captureOutput do discard <| humanReport .verbose #[sample "t" .pass]
  assertContains "ok    t" out.stdout

/--
Characters that XML 1.0 forbids are replaced with the canonical replacement character in the JUnit
report.
-/
@[test]
def junitReplacesForbiddenChars : Test := do
  let bad := (Char.ofNat 0xFFFF).toString ++ (Char.ofNat 0xFFFE).toString ++ (Char.ofNat 0x1).toString
  let r := sample "t" (.fail { message := s!"bad{bad}char\tkept" })
  let xml := junitReport { results := #[r], seed := 0 }
  assertContains "bad\uFFFD\uFFFD\uFFFDchar\tkept" xml
  assertTrue (!xml.contains (Char.ofNat 0xFFFF) && !xml.contains (Char.ofNat 0xFFFE))
  assertTrue (!xml.contains (Char.ofNat 0x1))

/-- The JUnit report includes a failing test's captured output, one element per stream. -/
@[test]
def junitIncludesOutput : Test := do
  let output : OutputLog := { log := #[.stdout "out 1\n", .stderr "err <1>\n", .stdout "out 2\n"] }
  let r := sample "t" (.fail { message := "boom" }) (output := output)
  let xml := junitReport { results := #[r], seed := 0 }
  assertContains "<system-out>out 1\nout 2\n</system-out>" xml
  assertContains "<system-err>err &lt;1&gt;\n</system-err>" xml

/-- The JUnit report omits the output elements for a test that produced no output. -/
@[test]
def junitOmitsEmptyOutput : Test := do
  let xml := junitReport { results := #[sample "t" .pass], seed := 0 }
  assertNotContains "system-out" xml
  assertNotContains "system-err" xml

/-- A test's results are truncated after the cap at quiet verbosity, with a summary, but not at verbose. -/
@[test]
def reportTruncates : Test := do
  let many := (Array.range 60).map fun i => sample "many" .pass (resultPath := #[s!"case {i}"])
  let quiet ← captureOutput do discard <| humanReport .quiet many
  assertBEq 51 (quiet.stdout.splitOn "ok    ").length
  -- The summary lines up with the named results' rows, which are one level deep.
  assertContains "\n      (... and 10 more passed)" quiet.stdout
  let verbose ← captureOutput do discard <| humanReport .verbose many
  assertBEq 61 (verbose.stdout.splitOn "ok    ").length
  assertBEq 1 (verbose.stdout.splitOn "(... and").length

/--
Truncation never suppresses a failure or error: past the cap they print in full and only the passes
around them are summarized.
-/
@[test]
def reportTruncationShowsFailures : Test := do
  let many := (Array.range 60).map fun i =>
    let v : Verdict := if i == 55 then .fail { message := "boom" } else .pass
    sample "many" v (resultPath := #[s!"case {i}"])
  let quiet ← captureOutput do discard <| humanReport .quiet many
  -- The named results have no parent line, so the failure is named in full.
  assertContains "\nFAIL  many.case 55: boom" quiet.stdout
  assertContains "(... and 9 more passed)" quiet.stdout

/-- `humanReport` returns the number of failures, errors, and inconclusive results. -/
@[test]
def reportFailureCount : Test := do
  let pass := sample "t" .pass
  let fail := sample "u" (.fail { message := "x" })
  let err := sample "v" (.error "oops")
  let lost : Result := { test := "w", outcome := .inconclusive (.exitedWithoutVerdict 2) }
  let count ← IO.mkRef 0
  discard <| captureOutput do count.set (← humanReport .silent #[pass, fail, err, lost])
  assertBEq 3 (← count.get)

/--
`markdownReport` gives a tally, an open collapsible per failure, and a table per test executable.
-/
@[test]
def reportMarkdown : Test := do
  let pass := sample "t" .pass (exe := "E")
  let f : TestFailure := { message := "boom", detail? := some "expected 1\nactual 2" }
  let fail := sample "u" (.fail f) (exe := "E")
  let md := markdownReport { results := #[pass, fail], seed := 0 }
  assertContains "**1** passed · **1** failed · **0** errors · **0** inconclusive" md
  assertContains "<details open><summary>❌ <code>E</code> u: boom</summary>" md
  assertContains "expected 1\nactual 2" md
  assertContains "Summary by test executable" md

/--
JUnit has a suite per test executable, and a test's class is its path without its last component, or
the executable's name for a test whose path has one component.
-/
@[test]
def junitSuitesAndClasses : Test := do
  let deep : Result := { exe := "Lib", test := "A.B.t", path := #["A", "B", "t"], outcome := .reported .pass }
  let flat : Result := { exe := "Other", test := "u", path := #["u"], outcome := .reported .pass }
  let xml := junitReport { results := #[deep, flat], seed := 0 }
  assertContains "<testsuite name=\"Lib\"" xml
  assertContains "<testsuite name=\"Other\"" xml
  assertContains "name=\"A.B.t\" classname=\"A.B\"" xml
  assertContains "name=\"u\" classname=\"Other\"" xml

/-- `runValue` reports a passing value as passed. -/
@[test]
def runOnePasses : Test := do
  let o ← runValue default (pure () : Test)
  assertBEq .passed o.status

/-- `runValue` reports a failing value as failed and carries its message. -/
@[test]
def runOneFails : Test := do
  let o ← runValue default (TestResult.fail { message := "boom" })
  assertBEq .failed o.status
  assertBEq (some "boom") o.message?

/-- A failing run surfaces its captured output in the outcome. -/
@[test]
def runOneCapturesOutput : Test := do
  let o ← runValue default (do IO.println "trace line"; failHere "nope" : Test)
  assertBEq .failed o.status
  assertBEq 1 o.allOutput.size
  assertBEq .stdout o.allOutput[0]!.stream
  assertContains "trace line" o.allOutput[0]!.text

/--
An outcome takes the most severe verdict among a test and its named results, with the message of
the innermost result that has it, which is where the assertion failed.
-/
@[test]
def runOneAggregates : Test := do
  let o ← runValue default (do result "a" (pure ()); result "b" (failHere "bad") : Test)
  assertBEq .failed o.status
  assertBEq (some "bad") o.message?

/--
An outcome reports one scope per result: the test's own first, then the named results in the order
they started, each naming the scope that contains it.
-/
@[test]
def runOneNodes : Test := do
  let o ← runValue default (do
    result "a" (result "inner" (pure ()))
    result "b" (failHere "bad") : Test)
  assertBEq #["", "a", "inner", "b"] (o.results.map (·.name))
  assertBEq #[0, 0, 1, 0] (o.results.map (·.parent))
  assertBEq #[0, 1, 2, 3] (o.results.map (·.id))
  assertBEq #[some .failed, some .passed, some .passed, some .failed]
    (o.results.map (·.status?))
  result "the failure's message is on the result that raised it" do
    assertBEq (some "bad") o.results[3]!.message?

/-- Each scope of an outcome holds what its own code wrote, and what a scope inside it wrote is there. -/
@[test]
def runOneNodeOutput : Test := do
  let o ← runValue default <| show Test from do
    IO.println "outer"
    result "inner" (IO.println "within")
    IO.println "after"
  let text (node : ResultNode) : String := node.output.foldl (fun acc c => acc ++ c.text) ""
  assertBEq #["outer\nafter\n", "within\n"] (o.results.map text)

/--
A named result and the action of an `expectFail` are each reported as they start and again as they
finish, with reports properly nested.
-/
@[test]
def runOneWatchesResults : Test := do
  let seen ← IO.mkRef (#[] : Array String)
  let watch (ev : ResultEvent) : IO Unit :=
    let said :=
      match ev with
      | .started path => "start " ++ ".".intercalate path.toList
      | .finished r => "end " ++ ".".intercalate r.resultPath.toList
      | .expectFailStarted => "expecting"
      | .expectFailFinished expected => s!"expected {expected}"
    seen.modify (·.push said)
  let _ ← runValue default  (watch := watch) do
    result "a" (result "inner" (pure ()))
    result "b" (pure ())
    expectFail (result "c" (fail "boom"))
  assertBEq
    #["start a", "start a.inner", "end a.inner", "end a", "start b", "end b",
      "expecting", "start c", "end c", "expected true"]
    (← seen.get)

/-- An outcome includes warnings for unused options. -/
@[test]
def runOneUnreadOptions : Test := do
  let reads : Test := do
    let _ ← flag "read"
  let options := #[("read", ""), ("zeta", "1"), ("alpha", "2"), ("alpha", "3")]
  let o ← runEntryOutcome (.of "" "" "" default reads) (options := options)
  assertBEq #["alpha", "zeta"] o.unreadOptions
  result "a test given no options has none unread" do
    let o ← runEntryOutcome (.of "" "" "" default reads)
    assertBEq #[] o.unreadOptions

/-- An outcome with some optional fields set, used to test its JSON encoding. -/
private def sampleOutcome : RunOutcome where
  status := .failed
  durationMs := 5
  message? := some "bad"
  seed? := some "7"
  options := #[{ name := "a", value := "1" }]
  unreadOptions := #["a"]


/-- Decoding an outcome's JSON gives back the outcome. -/
@[test]
def runOutcomeJsonRoundTrips : Test := do
  let decoded ← IO.ofExcept (Lean.fromJson? (α := RunOutcome) (Lean.toJson sampleOutcome))
  assertBEq (Lean.toJson sampleOutcome).compress (Lean.toJson decoded).compress

/-- An outcome's JSON has no key for an optional field that is {lean}`none`. -/
@[test]
def runOutcomeJsonOmitsNone : Test := do
  assertTrue ((Lean.toJson sampleOutcome).getObjVal? "detail").toOption.isNone

/-- Decoding JSON that is missing a key gives that field of the outcome its default value. -/
@[test]
def runOutcomeJsonDefaults : Test := do
  let minimal := Lean.Json.mkObj
    [("status", Lean.toJson ResultNode.Status.passed), ("durationMs", Lean.toJson 1)]
  let decoded ← IO.ofExcept (Lean.fromJson? (α := RunOutcome) minimal)
  assertBEq 0 decoded.results.size
  assertBEq 0 decoded.options.size
  assertBEq #[] decoded.unreadOptions
  assertBEq none decoded.seed?

/-- A passing run still surfaces its captured output. -/
@[test]
def runOnePassOutput : Test := do
  let o ← runValue default (do IO.println "printed"; return true : IO Bool)
  assertBEq .passed o.status
  assertBEq 1 o.allOutput.size
  assertBEq .stdout o.allOutput[0]!.stream
  assertContains "printed" o.allOutput[0]!.text

/-- Captured output keeps stdout and stderr distinct and interleaved in order. -/
@[test]
def runOneStreams : Test := do
  let o ← runValue default <| show IO Bool from do
    IO.println "out one"
    IO.eprintln "err one"
    IO.println "out two"
    return true
  assertBEq .passed o.status
  assertBEq 3 o.allOutput.size
  assertBEq .stdout o.allOutput[0]!.stream
  assertBEq .stderr o.allOutput[1]!.stream
  assertBEq .stdout o.allOutput[2]!.stream

/-- `failure` from the `Alternative` instance fails a test. -/
@[test]
def alternativeFailure : Test := expectFail failure

/-- `<|>` recovers from an assertion failure by running the alternative. -/
@[test]
def alternativeOrElse : Test := failure <|> assertBEq 1 1

/-- The names of the settings in the settings fixture module: their fully qualified names. -/
private def greetingName : String := "ErrataTests.Settings.greeting"
@[inherit_doc greetingName] private def repeatsName : String := "ErrataTests.Settings.repeats"
@[inherit_doc greetingName] private def quietName : String := "ErrataTests.Settings.quiet"

/-- The test in the settings fixture module that takes settings. -/
private def greetsEntry : TestM TestEntry := do
  let some e := (getAllTests% "verso" ErrataTests.Settings).find? (·.name == "ErrataTests.Settings.greets")
    | fail "the test that takes settings is missing"
  return e

/--
A test's entry carries its tags and the settings it takes, in the order of its parameters, each with
its description and its declared default.
-/
@[test]
def testsCarryTagsAndSettings : Test := do
  let e ← greetsEntry
  assertBEq #["slow", "chatty"] e.tags
  assertBEq #[greetingName, repeatsName, quietName] (e.settings.map (·.name))
  assertBEq #[false, false, true] (e.settings.map (·.optional))
  assertBEq #[some "hello", some "2", none] (e.settings.map (·.default?))
  assertBEq (some "The word that a test greets with.")
    (e.settings[0]?.bind (·.description?) |>.map (·.trimAscii.copy))
  let some plain := (getAllTests% "verso" ErrataTests.Settings).find? (·.name == "ErrataTests.Settings.plain")
    | fail "the plain test is missing"
  assertBEq #[] plain.tags
  assertBEq 0 plain.settings.size

/--
A test's action parses the values of the settings it takes and applies the test to them. The last
value given for a setting counts, an optional setting without a value is `none`, and a missing
mandatory setting or a value its parser rejects ends the test with an error that names the setting.
-/
@[test]
def settingsAreParsed : Test := do
  let e ← greetsEntry
  let run (settings : Array (String × String)) : TestM Result := do
    let rs ← runEntry (← mkContext) e settings
    let some r := rs[0]? | fail "the test has no result"
    return r
  result "values reach the test" do
    let r ← run #[(greetingName, "hi"), (repeatsName, "1"), (repeatsName, "3")]
    assertTrue r.status.isSuccess
    assertBEq "hi\nhi\nhi\n" r.output.stdout
  result "an optional setting" do
    let r ← run #[(greetingName, "hi"), (repeatsName, "3"), (quietName, "true")]
    assertTrue r.status.isSuccess
    assertBEq "" r.output.stdout
  result "a missing mandatory setting" do
    match (← run #[(greetingName, "hi")]).status with
    | .error m => assertContains s!"the mandatory setting {repeatsName} has no value" m
    | s => fail s!"expected an error, got {repr s}"
  result "a value that the parser rejects" do
    match (← run #[(greetingName, "hi"), (repeatsName, "many")]).status with
    | .error m => assertContains s!"the setting {repeatsName} has the value \"many\"" m
    | s => fail s!"expected an error, got {repr s}"
  result "an optional value that the parser rejects" do
    match (← run #[(greetingName, "hi"), (repeatsName, "1"), (quietName, "maybe")]).status with
    | .error m => assertContains s!"the setting {quietName} has the value \"maybe\"" m
    | s => fail s!"expected an error, got {repr s}"
  result "a setting's last name component is not its name" do
    match (← run #[("greeting", "hi"), ("repeats", "1")]).status with
    | .error m => assertContains s!"the mandatory setting {greetingName} has no value" m
    | s => fail s!"expected an error, got {repr s}"

/--
The Lean harness lists the settings that its tests take before the tests, each once, with its
description and its default, and each test with its tags and the settings it takes.
-/
@[test]
def harnessListsSettings : Test := do
  let e ← greetsEntry
  IO.FS.withTempDir fun dir => do
    let out := dir / "out.jsonl"
    IO.FS.writeFile out ""
    assertBEq 0 (← Harness.dispatch #[e, e] ["errata-list", out.toString])
    let lines := (← IO.FS.readFile out).splitOn "\n" |>.filter (!·.isEmpty)
    let records := lines.filterMap fun l =>
      match Protocol.Record.parseLine l with
      | .ok (some (_, r)) => some r
      | _ => none
    match records with
    | [.protocol _, .setting (some g) (some d) (some "hello"), .setting (some r) _ (some "2"),
        .setting (some q) _ none, .test info, .test _] =>
      assertBEq #[greetingName, repeatsName, quietName] #[g, r, q]
      assertContains "greets with" d
      assertBEq (some #["slow", "chatty"]) info.tags?
      assertBEq
        (some #[{ name := greetingName }, { name := repeatsName }, { name := quietName, optional := true }])
        info.settings?
    | _ => fail s!"unexpected records: {lines}"

/--
error: `hiddenSetting` is private or not exported, so a test executable cannot reach it. Make it public, for example by declaring it in a `public section`.
-/
#test_msgs in
@[setting] private def hiddenSetting : Setting where
  type := Nat
  fromString s := s.toNat?

/--
error: `unexposedSetting` must expose its value to the modules that import it, so that a test's parameter has the setting's type there. Mark it `@[expose]`, or declare it with `abbrev`.
-/
#test_msgs in
@[setting] def unexposedSetting : Setting where
  type := Nat
  fromString s := s.toNat?

-- An `abbrev` exposes its value, so it is a setting without `@[expose]`.
#test_msgs in
@[setting] abbrev abbreviatedSetting : Setting where
  type := Nat
  fromString s := s.toNat?

/--
error: `@[setting]` requires the type `Errata.Setting`, and `notASetting` has the type
  Nat
-/
#test_msgs in
@[setting, expose] def notASetting : Nat := 3

-- A setting's name is its fully qualified name, so settings whose names end alike are distinct.
#test_msgs in
@[setting, expose] def greeting : Setting where
  type := String
  fromString s := some s

/--
error: `instanceParameter` has an instance parameter of type
  Inhabited Nat
A test's parameters are settings: `S` or `Option S` for a declaration `S` marked `@[setting]`.
-/
#test_msgs in
@[test] def instanceParameter [Inhabited Nat] : Bool := true

/--
error: The parameter `n` of `implicitParameter` is implicit. A test's parameters are explicit settings. A setting named before its declaration becomes an implicit parameter when `autoImplicit` is on, so declare the setting before the test.
-/
#test_msgs in
@[test] def implicitParameter {n : seed} : Bool := n == n

/-- Another name for the seed setting. -/
abbrev SeedAlias := seed

/--
error: The parameter `n` of `aliasParameter` has the type `SeedAlias`, which stands for the setting `Errata.seed`. A test names a setting directly: write `Errata.seed`.
-/
#test_msgs in
@[test] def aliasParameter (n : SeedAlias) : Bool := n == n

/--
error: The parameter `laterSetting` of `usedBeforeDeclaration` is implicit. A test's parameters are explicit settings. A setting named before its declaration becomes an implicit parameter when `autoImplicit` is on, so declare the setting before the test.
-/
#test_msgs in
set_option autoImplicit true in
@[test] def usedBeforeDeclaration (_x : laterSetting) : Bool := true

/--
error: The parameter `n` of `takesNat` has the type
  Nat
which is not a setting. A test's parameters are settings: `S` or `Option S` for a declaration `S` marked `@[setting]`.
-/
#test_msgs in
@[test] def takesNat (n : Nat) : Bool := n == n

/-- error: `@[test]` has no argument `flavor`; its one argument is `tags` -/
#test_msgs in
@[test (flavor := sweet)] def flavored : Bool := true

-- A partial application of `property` is a test that takes the seed.
#test_msgs in
@[test] def partialProperty : seed → Test := property (∀ n : Nat, n + 0 = n)

-- Two guards whose first source line is identical must get distinct generated names.
#test_guard 1 + 1 == 2
#test_guard 1 + 1 == 2
