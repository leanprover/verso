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
public meta import Errata
import all Errata.FS
import all ErrataTests.Fixture
import all ErrataTests.Fixture.Sub
import all ErrataTests.Docstrings

open Errata

/-- A bare boolean is a passing test. -/
@[test]
def onePlusOne : Bool := 1 + 1 == 2

/-- An assertion-based test. -/
@[test]
def equality : Test := do
  assertEq 4 (2 + 2)

/-- A test with named results. -/
@[test]
def named : Test := do
  result "first" (assertEq 1 1)
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
  expectFail (assertEq 1 2)

/-- A data-driven family expressed as a plain loop. -/
@[test]
def squares : Test := do
  for (n, sq) in [(1, 1), (2, 4), (3, 9)] do
    result s!"square {n}" (assertEq sq (n * n))

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
error: Module `NoSuchModule` is not imported, so its tests cannot be reached. Import it, using `import all NoSuchModule` if it belongs to the module system.
-/
#test_msgs in
example : Array TestEntry := getAllTests% "verso" NoSuchModule

/-- A module below several named roots contributes its tests once. -/
@[test]
def discoveryDeduplicates : Test := do
  -- `ErrataTests.Fixture.Sub` lies below both roots, so exactly the two fixture tests are found.
  let entries := (getAllTests% "verso" ErrataTests.Fixture ErrataTests.Fixture.Sub)
  assertEq 2 entries.size

/-- The docstring of a test in the docstring fixture module, when it has one. -/
private def fixtureDocstring (test : String) : Option String :=
  (getAllTests% "verso" ErrataTests.Docstrings).find? (·.test == test) |>.bind (·.docstring?)

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
  let some doc := fixtureDocstring "customRoleDoc" | assertTrue false "docstring missing"
  assertContains "Refers to `ErrataTests.Docstrings.docstringTarget`, whose name" doc

/-- A test's docstring travels with its results. -/
@[test]
def docstringReachesResults : Test := do
  let cfg ← mkContext
  let results ← runEntry cfg <|
    TestEntry.of "p" "M" "documented" { file := "f", startPos := ⟨0, 0⟩, endPos := ⟨0, 0⟩ }
      (pure () : Test) (docstring? := some "What it checks.")
  assertTrue (results.all (·.description? == some "What it checks."))

/--
The human-readable report shows a failure's docstring, indented below its status line, and shows a
pass's docstring only when every docstring is shown.
-/
@[test]
def reportShowsDocstring : Test := do
  let pass : Result :=
    { package := "p", moduleName := "M", test := "t", status := .pass,
      description? := some "Passing doc." }
  let fail : Result :=
    { package := "p", moduleName := "M", test := "u", status := .fail { message := "boom" },
      description? := some "Failing doc.
Second line." }
  let silent ← captureOutput do discard <| humanReport .silent #[pass, fail]
  assertContains "FAIL  p/M  u: boom\n    Failing doc.\n    Second line.\n" silent.stdout
  assertNotContains "Passing doc." silent.stdout
  let verbose ← captureOutput do discard <| humanReport .verbose #[pass]
  assertNotContains "Passing doc." verbose.stdout
  let all ← captureOutput do discard <| humanReport .superVerbose #[pass]
  assertContains "ok    p/M  t" all.stdout
  assertContains "\n    Passing doc.\n" all.stdout

/-- The Markdown report includes a failure's docstring as Markdown. -/
@[test]
def markdownReportShowsDocstring : Test := do
  let fail : Result :=
    { package := "p", moduleName := "M", test := "u", status := .fail { message := "boom" },
      description? := some "Checks `x` and **y**." }
  assertContains "u: boom</summary>\n\nChecks `x` and **y**.\n\n" (markdownReport #[fail])

/-- A property test. -/
@[test]
def addComm : Test :=
  property (∀ a b : Nat, a + b = b + a)

open Lean (toJson fromJson?)

deriving instance Plausible.Shrinkable, Plausible.Arbitrary for Lean.Position
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for Location
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for TestFailure
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for Status
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for Output
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for OutputLog
deriving instance Plausible.Shrinkable, Plausible.Arbitrary for Result

/-- The JSON encoding of a result round-trips: decoding the encoding recovers the result. -/
@[test]
def jsonRoundTrips : Test :=
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

/-- Runs one action as a test in a fresh context, returning the results it recorded. -/
private def resultsOf (act : Test) : TestM (Array Result) := do
  let cfg ← mkContext
  runEntry cfg <|
    TestEntry.of "p" "M" "inner" { file := "f", startPos := ⟨0, 0⟩, endPos := ⟨0, 0⟩ } act

/-- A missing produced directory is a golden failure at the call site, not a bare error. -/
@[test]
def goldenDirReportsMissingOutput : Test := do
  let results ← IO.FS.withTempDir fun dir =>
    resultsOf (goldenDir (dir / "expected") (dir / "never-created"))
  assertEq 1 results.size
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
  assertEq 1 results.size
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
  assertEq 1 results.size
  assertTrue results[0]!.status.isSuccess

/-- A file where a directory was expected is a golden failure, not a raw error. -/
@[test]
def goldenDirRejectsNonDirectory : Test := do
  let results ← IO.FS.withTempDir fun dir => do
    let actual := dir / "actual"
    IO.FS.writeFile actual "not a directory\n"
    resultsOf (goldenDir (dir / "expected") actual)
  assertEq 1 results.size
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
  assertEq 1 results.size
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
  assertEq 1 results.size
  assertTrue (results[0]!.status matches .fail _)

/-- Output written before a failure reaches the enclosing result, where it explains the failure. -/
@[test]
def captureOutputKeepsOutputOnFailure : Test := do
  let results ← resultsOf (discard <| captureOutput (do IO.println "diagnostic"; fail "boom"))
  assertEq 1 results.size
  let r := results[0]!
  assertTrue (r.status matches .fail _)
  assertContains "diagnostic" r.output.all

/-- Output from an action that completes stays with the capture, rather than reaching the result. -/
@[test]
def captureOutputDivertsOnSuccess : Test := do
  let results ← resultsOf do
    let captured ← captureOutput (IO.println "quiet")
    assertContains "quiet" captured.all
  assertEq 1 results.size
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
  assertEq "é" captured.stdout

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
  assertEq "a😀" captured.stdout

/-- Bytes whose code point is never completed are an error, not silently dropped. -/
@[test]
def captureRejectsDanglingBytes : Test := do
  let results ← resultsOf do
    let out ← IO.getStdout
    out.write ("é".toUTF8.extract 0 1)
  assertEq 1 results.size
  assertTrue (results[0]!.status matches .error _)

/-- The invocation that these tests hand to the runner. -/
def testInvocation : Invocation := { run := "lake test", runner := "lake test -- --test-options" }

/--
The flag that these tests use to mark a runner as started by the driver.

This is deliberately not the canonical one defined in the Lake config, so that we test that the generated code works with _whatever_ is passed and that the value is not hard-coded twice.
-/
def testDriverFlag : String := "--from-driver"

/--
Under --wfail, an option that no test reads causes the run to fail instead of only issuing a
warning.
-/
@[test]
def wfailPromotesUnusedOptions : Test := do
  let entry := TestEntry.of "p" "M" "t"
    { file := "f", startPos := ⟨0, 0⟩, endPos := ⟨0, 0⟩ } (pure () : Test)
  let lax ← IO.mkRef (0 : UInt32)
  let wfail ← IO.mkRef (0 : UInt32)
  discard <| captureOutput do
    lax.set (← runMain testInvocation #[entry] ["--", "--bogus=1"])
    wfail.set (← runMain testInvocation #[entry] ["--wfail", "--", "--bogus=1"])
  assertEq 0 (← lax.get)
  assertEq 1 (← wfail.get)

/-- The detail given to a true-assertion is attached to its failure. -/
@[test]
def assertTrueAttachesDetail : Test := do
  let results ← resultsOf (assertTrue false "boom" (detail? := some "why"))
  assertEq 1 results.size
  match results[0]!.status with
  | .fail f => assertEq (some "why") f.detail?
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
  assertEq "éxû" captured.stdout

/-- Text printed while a raw code point is unfinished is malformed output, not reordered output. -/
@[test]
def capturePrintDuringPartialWriteRejected : Test := do
  let results ← resultsOf do
    let out ← IO.getStdout
    out.write ("é".toUTF8.extract 0 1)
    IO.print "x"
  assertEq 1 results.size
  assertTrue (results[0]!.status matches .error _)

/-- Dangling bytes at the end of a failing test do not displace the test's own failure. -/
@[test]
def danglingBytesKeepFailure : Test := do
  let results ← resultsOf do
    let out ← IO.getStdout
    out.write ("é".toUTF8.extract 0 1)
    fail "the real failure"
  assertEq 1 results.size
  match results[0]!.status with
  | .fail f => assertEq "the real failure" f.message
  | s => fail s!"expected the assertion failure, got {repr s}"

/-- A raw write with no valid decoding is rejected at the write itself. -/
@[test]
def captureRejectsInvalidBytes : Test := do
  let results ← resultsOf do
    let out ← IO.getStdout
    out.write (ByteArray.mk #[0xFF])
  assertEq 1 results.size
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
  assertEq 1 (← depth.get)

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
  assertEq #["hi\n"] (← received.get)

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
    assertEq 1 (← calls.get)
  result "the failure is reported" do
    assertContains "live output destination failed" out.all

/-- A failure that a nested `result` recorded still satisfies `expectFail`. -/
@[test]
def expectFailSeesNestedResult : Test := do
  let results ← resultsOf (expectFail (result "inner" (assertEq 1 2)))
  assertEq 1 results.size
  assertTrue results[0]!.status.isSuccess

/-- An error inside `expectFail` is not an expected failure, even when a nested `result` records it. -/
@[test]
def expectFailRejectsNestedError : Test := do
  let results ← resultsOf <|
    expectFail (result "inner" (show IO Unit from throw (.userError "broken setup")))
  assertTrue (results.any (!·.status.isSuccess))

/-- An error inside `expectFail` stands even when a sibling result recorded a failure. -/
@[test]
def expectFailKeepsErrorBesideFailure : Test := do
  let results ← resultsOf <| expectFail do
    result "a" <| assertEq 1 2
    result "b" <| show IO Unit from throw (.userError "broken setup")
  assertTrue (results.any (·.status matches .error _))

/-- A nested failure satisfies `expectFail` whether or not the action goes on to throw. -/
@[test]
def expectFailAgreesAcrossPaths : Test := do
  let thrown ← resultsOf (expectFail (do result "a" (assertEq 1 2); assertEq 3 4))
  let recorded ← resultsOf (expectFail (do result "a" (assertEq 1 2); result "b" (assertEq 3 4)))
  result "action throws afterwards" (assertTrue (thrown.all (·.status.isSuccess)))
  result "action records only" (assertTrue (recorded.all (·.status.isSuccess)))

/-- Results other than the expected failure survive `expectFail`. -/
@[test]
def expectFailKeepsPassingResults : Test := do
  let results ← resultsOf <| expectFail do
    result "ok" (assertEq 1 1)
    result "a" (assertEq 1 2)
  assertTrue (results.any (fun r => r.status.isSuccess && r.testName.endsWith "ok"))

-- `here%` reports its own position, so the expected column below is the indentation of the line it
-- sits on, and the expected span is the five characters of the token itself.
def indentedHere : Location :=
  here%

/-- Source positions follow Lean's convention: lines count from one and columns from zero. -/
@[test]
def positionConvention : Test := do
  assertEq 2 indentedHere.startPos.column
  assertEq 5 (indentedHere.endPos.column - indentedHere.startPos.column)

/-- The `Verbosity` predicates behave as the report relies on. -/
@[test]
def verbosityLevels : Test := do
  assertEq false Verbosity.silent.showsPasses
  assertEq true Verbosity.quiet.showsPasses
  assertEq true Verbosity.verbose.showsPasses
  assertEq true Verbosity.superVerbose.showsPasses
  assertEq false Verbosity.silent.truncates
  assertEq true Verbosity.quiet.truncates
  assertEq false Verbosity.verbose.truncates
  assertEq false Verbosity.superVerbose.truncates
  assertEq false Verbosity.verbose.showsAllDocstrings
  assertEq true Verbosity.superVerbose.showsAllDocstrings

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

The fixture workspaces under `fixtures` require Verso (and thus Errata) by path. `driver-configured`
names Verso's driver as its test driver, so the command is `lake test`. `driver-shadowed` has an
`Errata.run` script of its own that a bare name would run, so Verso's must be named as
`verso/Errata.run`.

The driver's help should show the expected command.
-/
@[test]
def driverHelpNamesInvocation : Test := do
  let cases : List (String × Option System.FilePath × String) := [
    ("verso", none, "lake run Errata.run"),
    ("configured", some (fixturesDir / "driver-configured"), "lake test"),
    ("shadowed", some (fixturesDir / "driver-shadowed"), "lake run verso/Errata.run")]
  for (name, fixture?, run) in cases do
    result name do
      let args := #["run", "verso/Errata.run", "--help"]
      let out ← match fixture? with
        | some fixture => lakeInFixture fixture args
        | none => IO.Process.output { cmd := "lake", args }
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
because its tests are never discovered. The `--wfail` flag makes that report into an error. The
fixture's `AppStray` library has one such module.
-/
@[test]
def driverReportsUnreachableModules : Test := do
  let fixture := fixturesDir / "driver-configured"
  let notice := "modules are not reachable from their library's roots"
  result "A warning is emitted" do
    let out ← lakeInFixture fixture #["test", "--", "AppStray"]
    assertExitCode 0 out
    assertContains s!"warning: these {notice}" out.stderr
    assertContains "AppStray: AppStray.Orphan" out.stderr
    assertContains "1 passed, 0 failed, 0 errors" out.stdout
  result "The --wfail flag turns the warning into an error" do
    let out ← lakeInFixture fixture #["test", "--", "AppStray", "--test-options", "--wfail"]
    assertExitCode 1 out
    assertContains s!"error: these {notice}" out.stderr
    assertNotContains "passed" out.stdout

/-- The runner's help names the command that its options follow. -/
@[test]
def runnerHelpNamesInvocation : Test := do
  let out ← captureOutput do
    discard <| runMain testInvocation #[] ["--help"]
  assertContains s!"{testInvocation.runner} [FLAGS]" out.all

/--
The generated runner's entry point runs the tests when the driver's flag leads, and otherwise
explains how to run the tests and fails.
-/
@[test]
def driverMainChecksFlag : Test := do
  let entry := TestEntry.of "p" "M" "t"
    { file := "f", startPos := ⟨0, 0⟩, endPos := ⟨0, 0⟩ } (pure () : Test)
  let withFlag ← IO.mkRef (0 : UInt32)
  let withoutFlag ← IO.mkRef (0 : UInt32)
  let out ← captureOutput do
    withFlag.set (← driverMain testDriverFlag testInvocation #[entry] [testDriverFlag])
    withoutFlag.set (← driverMain testDriverFlag testInvocation #[entry] [])
  result "flag leads" do
    assertEq 0 (← withFlag.get)
  result "flag missing" do
    assertEq 1 (← withoutFlag.get)
    assertContains testInvocation.run out.all
    assertContains testDriverFlag out.all

/--
The generated runner starts only when the driver's flag is its first argument, and the flag is
removed before the runner's own options are parsed.
-/
@[test]
def driverInvocation : Test := do
  result "flag is removed" do
    assertEq (some ["-v", "--", "--x=1"])
      (checkInvocation testDriverFlag testInvocation [testDriverFlag, "-v", "--", "--x=1"]).toOption
  result "no arguments" do
    assertTrue (checkInvocation testDriverFlag testInvocation [] matches .error _)
  result "missing flag" do
    assertTrue (checkInvocation testDriverFlag testInvocation ["-v"] matches .error _)
  result "flag must come first" do
    assertTrue
      (checkInvocation testDriverFlag testInvocation ["-v", testDriverFlag] matches .error _)
  result "message says how to run the tests" do
    let .error msg := checkInvocation testDriverFlag testInvocation [] | fail "expected an error"
    assertTrue ((msg.splitOn testInvocation.run).length > 1) "message should name the command"
    assertTrue ((msg.splitOn testDriverFlag).length > 1) "message should name the flag"

/--
The runner's command line: the `-v` forms select the verbosity, declared flags parse, and options
for the tests go after `--`.
-/
@[test]
def runnerArgParsing : Test := do
  result "default verbosity" do
    assertEq (some Verbosity.silent) ((parseOptions []).toOption.map (·.verbosity))
  result "-v" do
    assertEq (some Verbosity.quiet) ((parseOptions ["-v"]).toOption.map (·.verbosity))
  result "--verbose" do
    assertEq (some Verbosity.quiet) ((parseOptions ["--verbose"]).toOption.map (·.verbosity))
  result "-vv" do
    assertEq (some Verbosity.verbose) ((parseOptions ["-vv"]).toOption.map (·.verbosity))
  result "-vvv" do
    assertEq (some Verbosity.superVerbose) ((parseOptions ["-vvv"]).toOption.map (·.verbosity))
  result "update-golden" do
    assertEq (some true) ((parseOptions ["--update-golden"]).toOption.map (·.updateGolden))
  result "seed" do
    assertEq (some (some 42)) ((parseOptions ["--seed", "42"]).toOption.map (·.seed))
  result "non-numeric seed rejected" do
    assertTrue ((parseOptions ["--seed", "x"]) matches .error _)
  result "junit path" do
    assertEq (some (some "r.xml")) ((parseOptions ["--junit", "r.xml"]).toOption.map (·.junitPath))
  result "missing junit path rejected" do
    assertTrue ((parseOptions ["--junit"]) matches .error _)
  result "test options after --" do
    let opts := (parseOptions ["--", "--golden", "on", "--flag=v=1", "--golden", "two"]).toOption
    assertEq (some #["on", "two"]) (opts.map (·.options.getD "golden" #[]))
    assertEq (some #["v=1"]) (opts.map (·.options.getD "flag" #[]))
  result "valueless test option" do
    assertEq (some #[""]) ((parseOptions ["--", "--fast"]).toOption.map (·.options.getD "fast" #[]))
  result "unknown flag rejected" do
    assertTrue ((parseOptions ["--golden", "on"]) matches .error _)
  result "misplaced library name diagnosed" do
    match parseOptions ["--verbose", "ErrataTests"] with
    | .error msg => assertContains "ErrataTests" msg
    | .ok _ => assertTrue false "expected an error"

/-- A run that discovers nothing fails: a test tool with no tests is a broken setup, not a pass. -/
@[test]
def emptyRunFails : Test := do
  let code ← IO.mkRef (0 : UInt32)
  let out ← captureOutput do
    code.set (← runMain testInvocation #[] [])
  assertContains "no tests were discovered" out.all
  assertEq 1 (← code.get).toNat

/-- At silent verbosity the report hides passes but shows failures and the summary line. -/
@[test]
def reportSilent : Test := do
  let pass : Result := { package := "p", moduleName := "M", test := "t", status := .pass }
  let fail : Result := { package := "p", moduleName := "M", test := "u", status := .fail { message := "boom" } }
  let out ← captureOutput do discard <| humanReport .silent #[pass, fail]
  assertContains "FAIL  p/M  u: boom" out.stdout
  assertContains "1 passed, 1 failed, 0 errors" out.stdout
  assertEq 1 (out.stdout.splitOn "ok    ").length

/-- At verbose verbosity the report shows passes too. -/
@[test]
def reportVerbose : Test := do
  let pass : Result := { package := "p", moduleName := "M", test := "t", status := .pass }
  let out ← captureOutput do discard <| humanReport .verbose #[pass]
  assertContains "ok    p/M  t" out.stdout

/--
Characters that XML 1.0 forbids are replaced with the canonical replacement character in the JUnit
report.
-/
@[test]
def junitReplacesForbiddenChars : Test := do
  let bad := (Char.ofNat 0xFFFF).toString ++ (Char.ofNat 0xFFFE).toString ++ (Char.ofNat 0x1).toString
  let r : Result := { package := "p", moduleName := "M", test := "t",
                      status := .fail { message := s!"bad{bad}char\tkept" } }
  let xml := junitReport #[r]
  assertContains "bad\uFFFD\uFFFD\uFFFDchar\tkept" xml
  assertTrue (!xml.contains (Char.ofNat 0xFFFF) && !xml.contains (Char.ofNat 0xFFFE))
  assertTrue (!xml.contains (Char.ofNat 0x1))

/-- The JUnit report carries a failing test's captured output, one element per stream. -/
@[test]
def junitCarriesOutput : Test := do
  let output : OutputLog := { log := #[.stdout "out 1\n", .stderr "err <1>\n", .stdout "out 2\n"] }
  let r : Result := { package := "p", moduleName := "M", test := "t",
                      status := .fail { message := "boom" }, output }
  let xml := junitReport #[r]
  assertContains "<system-out>out 1\nout 2\n</system-out>" xml
  assertContains "<system-err>err &lt;1&gt;\n</system-err>" xml

/-- The JUnit report omits the output elements for a test that produced no output. -/
@[test]
def junitOmitsEmptyOutput : Test := do
  let r : Result := { package := "p", moduleName := "M", test := "t", status := .pass }
  let xml := junitReport #[r]
  assertNotContains "system-out" xml
  assertNotContains "system-err" xml

/-- A test's results are truncated after the cap at quiet verbosity, with a summary, but not at verbose. -/
@[test]
def reportTruncates : Test := do
  let many := (Array.range 60).map fun i =>
    ({ package := "p", moduleName := "M", test := "many", resultPath := #[s!"case {i}"], status := .pass } : Result)
  let quiet ← captureOutput do discard <| humanReport .quiet many
  assertEq 51 (quiet.stdout.splitOn "ok    ").length
  assertContains "(... and 10 more passed)" quiet.stdout
  let verbose ← captureOutput do discard <| humanReport .verbose many
  assertEq 61 (verbose.stdout.splitOn "ok    ").length
  assertEq 1 (verbose.stdout.splitOn "(... and").length

/--
Truncation never suppresses a failure or error: past the cap they print in full and only the passes
around them are summarized.
-/
@[test]
def reportTruncationShowsFailures : Test := do
  let many := (Array.range 60).map fun i =>
    let status : Status := if i == 55 then .fail { message := "boom" } else .pass
    ({ package := "p", moduleName := "M", test := "many", resultPath := #[s!"case {i}"], status } : Result)
  let quiet ← captureOutput do discard <| humanReport .quiet many
  assertContains "FAIL  p/M  many.case 55: boom" quiet.stdout
  assertContains "(... and 9 more passed)" quiet.stdout

/-- `humanReport` returns the number of failures and errors. -/
@[test]
def reportFailureCount : Test := do
  let pass : Result := { package := "p", moduleName := "M", test := "t", status := .pass }
  let fail : Result := { package := "p", moduleName := "M", test := "u", status := .fail { message := "x" } }
  let err : Result := { package := "p", moduleName := "M", test := "v", status := .error "oops" }
  assertEq 2 (← humanReport .silent #[pass, fail, err])

/-- `markdownReport` gives a tally, an open collapsible per failure, and a per-module table. -/
@[test]
def reportMarkdown : Test := do
  let pass : Result := { package := "p", moduleName := "M", test := "t", status := .pass }
  let f : TestFailure := { message := "boom", detail? := some "expected 1\nactual 2" }
  let fail : Result := { package := "p", moduleName := "M", test := "u", status := .fail f }
  let md := markdownReport #[pass, fail]
  assertContains "**1** passed · **1** failed" md
  assertContains "<details open><summary>❌ <code>p/M</code> u: boom</summary>" md
  assertContains "expected 1\nactual 2" md
  assertContains "Summary by module" md

/-- `failure` from the `Alternative` instance fails a test. -/
@[test]
def alternativeFailure : Test := expectFail failure

/-- `<|>` recovers from an assertion failure by running the alternative. -/
@[test]
def alternativeOrElse : Test := failure <|> assertEq 1 1

-- Two guards whose first source line is identical must get distinct generated names.
#test_guard 1 + 1 == 2
#test_guard 1 + 1 == 2
