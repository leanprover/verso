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
error: Module `NoSuchModule` is not imported, so its tests cannot be reached. Import it, using `import all NoSuchModule` if it belongs to the module system.
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
      (result "check" (assertBEq 1 2) : Test) (docstring? := some "What it checks.")
  result "the test's own result has it" do
    assertTrue (results.any fun r =>
      r.resultPath.isEmpty && r.description? == some "What it checks.")
  result "a named result has none" do
    assertTrue (results.any fun r => r.resultPath == #["check"] && r.description?.isNone)
  result "the Markdown report shows it once" do
    assertBEq 2 ((markdownReport { results, seed := 0 }).splitOn "What it checks.").length

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
  assertContains "u: boom</summary>\n\nChecks `x` and **y**.\n\n"
    (markdownReport { results := #[fail], seed := 0 })

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
  assertBEq 0 (← lax.get)
  assertBEq 1 (← wfail.get)

/--
Runs the runner with every report written to a temporary directory, returning the exit code and the
JUnit, JSON, and Markdown reports.
-/
private def runReporting (entries : Array TestEntry) (args : List String) :
    TestM (UInt32 × String × String × String) :=
  IO.FS.withTempDir fun dir => do
    let xml := dir / "report.xml"
    let json := dir / "report.json"
    let md := dir / "report.md"
    let code ← IO.mkRef (0 : UInt32)
    discard <| captureOutput do
      code.set (← runMain testInvocation entries
        (["--junit", xml.toString, "--json", json.toString, "--markdown", md.toString] ++ args))
    return (← code.get, ← IO.FS.readFile xml, ← IO.FS.readFile json, ← IO.FS.readFile md)

/--
An option that no test reads is a warning in every report, with the way to make it fail the run.
Under `--wfail` it is an error. A run with nothing to report has no "Test run" suite.
-/
@[test]
def unusedOptionsReachReports : Test := do
  let entry := TestEntry.of "p" "M" "t" default (pure () : Test)
  result "absent without issues" do
    let (_, xml, _, _) ← runReporting #[entry] []
    assertNotContains "Test run" xml
  result "as a warning" do
    let (code, xml, _, md) ← runReporting #[entry] ["--", "--bogus=1"]
    assertBEq 0 code.toNat
    assertContains "<testsuite name=\"Test run\"" xml
    assertNotContains "<error" xml
    assertContains "never read: bogus" xml
    assertContains "--wfail" xml
    assertContains "never read: bogus" md
  result "as an error under --wfail" do
    let (code, xml, _, md) ← runReporting #[entry] ["--wfail", "--", "--bogus=1"]
    assertBEq 1 code.toNat
    assertContains "<error message=" xml
    assertContains "never read: bogus" xml
    assertContains "## ❌" md

/-- The seed for the run's property tests reaches the JSON and Markdown reports. -/
@[test]
def seedReachesReports : Test := do
  let entry := TestEntry.of "p" "M" "t" default (pure () : Test)
  let (_, _, json, md) ← runReporting #[entry] ["--seed", "7"]
  let .ok j := Lean.Json.parse json | fail "the JSON report does not parse"
  assertBEq (some 7) (j.getObjValAs? Nat "seed").toOption
  assertContains "seed **7**" md

/-- A value from a wide range that is never shrunk, so that a counterexample reflects the seed. -/
private structure Wide where
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

/-- Runs a test with the given seed, or a fresh one, returning the seed used and the results. -/
private def seededResults (seed? : Option Nat) (act : Test) : TestM (Nat × Array Result) := do
  let cfg ← mkContext (seed := seed?)
  return (cfg.seed, ← runEntry cfg (TestEntry.of "p" "M" "t" default act))

/--
A failed property's detail names the seed that produced its counterexample, and running again with
that seed produces the same counterexample. Another seed produces another counterexample.
-/
@[test]
def propertySeedReplays : Test := do
  let wide : Test := property (∀ x : Wide, x.n ≠ x.n)
  let (seed, first) ← seededResults none wide
  let some detail := failDetail? first[0]! | fail "expected the property to fail"
  -- The counterexample is the detail's first paragraph.
  let counterexample (detail : String) : String := (detail.splitOn "\n\n").headD detail
  result "the detail names the seed" do
    assertContains s!"--seed {seed}" detail
  result "the seed replays the counterexample" do
    let (_, again) ← seededResults (some seed) wide
    assertBEq (some (counterexample detail)) ((failDetail? again[0]!).map counterexample)
  result "another seed gives another counterexample" do
    let (_, other) ← seededResults (some (seed + 1)) wide
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

/-- A test that indexes past the end of an array, and so panics and continues with a default. -/
private def panicking : Test := do
  let xs : Array Nat := #[]
  -- An index that the compiler cannot fold away.
  let i ← IO.rand 0 0
  assertBEq 0 xs[i]!

/--
A panic prints a message and continues with a default value, so a test that panics can produce a
passing verdict. The panic message is captured with the test's stderr and makes its result an error,
unless the context ignores panics.
-/
@[test]
def panicIsAnError : Test := do
  result "reported as an error" do
    let results ← resultsOf panicking
    assertBEq 1 results.size
    match results[0]!.status with
    | .error m => assertContains "index out of bounds" m
    | s => fail s!"expected an error, got {repr s}"
  result "ignored on request" do
    let cfg ← mkContext (ignorePanics := true)
    let results ← runEntry cfg (TestEntry.of "p" "M" "t" default panicking)
    assertBEq 1 results.size
    assertTrue results[0]!.status.isSuccess "the panic leaves the pass alone"

/--
The runner reports a test that panics as an error and fails the run. `--ignore-panics` leaves the
test's own verdict in place, and `--exit-on-panic` stops the runner at the panic, whose message the
runtime prints as it exits. The fixture's `AppPanic` library has a test that indexes past the end of
an array.
-/
@[test]
def driverReportsPanics : Test := do
  let fixture := fixturesDir / "driver-configured"
  let panicked := "app/AppPanic  panicsThenPasses: "
  result "A panic is an error" do
    let out ← lakeInFixture fixture #["test", "--", "AppPanic"]
    assertExitCode 1 out
    assertContains s!"ERROR {panicked}panicked: Error: index out of bounds" out.stdout
    assertContains "1 passed, 0 failed, 1 errors" out.stdout
  result "The --ignore-panics flag leaves the verdict alone" do
    let out ← lakeInFixture fixture #["test", "--", "AppPanic", "--test-options", "--ignore-panics"]
    assertExitCode 0 out
    assertContains "2 passed, 0 failed, 0 errors" out.stdout
  result "The --exit-on-panic flag stops the runner at the panic" do
    let out ← lakeInFixture fixture #["test", "--", "AppPanic", "--test-options", "--exit-on-panic"]
    assertTrue (out.exitCode != 0) "the run does not succeed"
    assertContains "Error: index out of bounds" out.stderr
    assertNotContains "passed" out.stdout

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
A test in a dependency's library is reported under the dependency's package. The fixture requires
the `dep` package, whose `DepLib` library has one test.
-/
@[test]
def dependencyTestsKeepTheirPackage : Test := do
  let fixture := fixturesDir / "driver-configured"
  IO.FS.withTempDir fun dir => do
    let junit := dir / "report.xml"
    let out ← lakeInFixture fixture
      #["test", "--", "dep/DepLib", "--test-options", "-v", "--junit", junit.toString]
    assertExitCode 0 out
    assertContains "ok    dep/DepLib  depTest" out.stdout
    assertContains "package=\"dep\"" (← IO.FS.readFile junit)

/--
A legacy root that imports a module-system child, each with a test, has each test discovered once:
the child's through the bridge and the root's through the main. The fixture's `AppMixed` library
has that shape, and the child's test is private to its module.
-/
@[test]
def mixedDiscoveryRunsEachTestOnce : Test := do
  let out ← lakeInFixture (fixturesDir / "driver-configured")
    #["test", "--", "AppMixed", "--test-options", "-v"]
  assertExitCode 0 out
  assertContains "ok    app/AppMixed  parentTest" out.stdout
  assertContains "ok    app/AppMixed.Child  childTest" out.stdout
  assertBEq 2 (out.stdout.splitOn "childTest").length
  assertContains "2 passed, 0 failed, 0 errors" out.stdout

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
    assertContains "FAIL  app/AppShadow.Failing  failsAsWritten" out.stdout
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
  let own := "FAIL  somePkg/SomeFile  inner: a named result did not pass\n" ++
    "    SomeFile.lean:42:23\n    output:\n    setup\n"
  assertContains own out.stdout
  -- The named result follows the test's own result.
  assertContains "\n  FAIL  check: " ((out.stdout.splitOn own)[1]?.getD "")
  assertContains "0 passed, 2 failed, 0 errors" out.stdout
  assertBEq 2 (← failures.get)

/-- Named results print indented under their test by their own names, siblings included. -/
@[test]
def reportIndentsNamedResultsUnderTheirParent : Test := do
  let results ← resultsOf do
    result "b" (pure ())
    result "c" (result "d" (pure ()))
  let out ← captureOutput do discard <| humanReport .verbose results
  assertTrue (out.stdout.startsWith "ok    somePkg/SomeFile  inner (")
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
    assertBEq 0 (← withFlag.get)
  result "flag missing" do
    assertBEq 1 (← withoutFlag.get)
    assertContains testInvocation.run out.all
    assertContains testDriverFlag out.all

/--
The generated runner starts only when the driver's flag is its first argument, and the flag is
removed before the runner's own options are parsed.
-/
@[test]
def driverInvocation : Test := do
  result "flag is removed" do
    assertBEq (some ["-v", "--", "--x=1"])
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
    assertBEq (some Verbosity.silent) ((parseOptions []).toOption.map (·.verbosity))
  result "-v" do
    assertBEq (some Verbosity.quiet) ((parseOptions ["-v"]).toOption.map (·.verbosity))
  result "--verbose" do
    assertBEq (some Verbosity.quiet) ((parseOptions ["--verbose"]).toOption.map (·.verbosity))
  result "-vv" do
    assertBEq (some Verbosity.verbose) ((parseOptions ["-vv"]).toOption.map (·.verbosity))
  result "-vvv" do
    assertBEq (some Verbosity.superVerbose) ((parseOptions ["-vvv"]).toOption.map (·.verbosity))
  result "update-golden" do
    assertBEq (some true) ((parseOptions ["--update-golden"]).toOption.map (·.updateGolden))
  result "seed" do
    assertBEq (some (some 42)) ((parseOptions ["--seed", "42"]).toOption.map (·.seed))
  result "non-numeric seed rejected" do
    assertTrue ((parseOptions ["--seed", "x"]) matches .error _)
  result "junit path" do
    assertBEq (some (some "r.xml")) ((parseOptions ["--junit", "r.xml"]).toOption.map (·.junitPath))
  result "missing junit path rejected" do
    assertTrue ((parseOptions ["--junit"]) matches .error _)
  result "test options after --" do
    let opts := (parseOptions ["--", "--golden", "on", "--flag=v=1", "--golden", "two"]).toOption
    assertBEq (some #["on", "two"]) (opts.map (·.options.getD "golden" #[]))
    assertBEq (some #["v=1"]) (opts.map (·.options.getD "flag" #[]))
  result "valueless test option" do
    assertBEq (some #[""]) ((parseOptions ["--", "--fast"]).toOption.map (·.options.getD "fast" #[]))
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
  assertBEq 1 (← code.get).toNat

/--
Every report records a run that discovered nothing as a failed run: JUnit has a "Test run" suite
with an error case, the JSON object lists the issue, and the Markdown headline is red.
-/
@[test]
def emptyRunReachesReports : Test := do
  let (code, xml, json, md) ← runReporting #[] []
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
  let pass : Result := { package := "p", moduleName := "M", test := "t", status := .pass }
  let fail : Result := { package := "p", moduleName := "M", test := "u", status := .fail { message := "boom" } }
  let out ← captureOutput do discard <| humanReport .silent #[pass, fail]
  assertContains "FAIL  p/M  u: boom" out.stdout
  assertContains "1 passed, 1 failed, 0 errors" out.stdout
  assertBEq 1 (out.stdout.splitOn "ok    ").length

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
  let xml := junitReport { results := #[r], seed := 0 }
  assertContains "bad\uFFFD\uFFFD\uFFFDchar\tkept" xml
  assertTrue (!xml.contains (Char.ofNat 0xFFFF) && !xml.contains (Char.ofNat 0xFFFE))
  assertTrue (!xml.contains (Char.ofNat 0x1))

/-- The JUnit report includes a failing test's captured output, one element per stream. -/
@[test]
def junitIncludesOutput : Test := do
  let output : OutputLog := { log := #[.stdout "out 1\n", .stderr "err <1>\n", .stdout "out 2\n"] }
  let r : Result := { package := "p", moduleName := "M", test := "t",
                      status := .fail { message := "boom" }, output }
  let xml := junitReport { results := #[r], seed := 0 }
  assertContains "<system-out>out 1\nout 2\n</system-out>" xml
  assertContains "<system-err>err &lt;1&gt;\n</system-err>" xml

/-- The JUnit report omits the output elements for a test that produced no output. -/
@[test]
def junitOmitsEmptyOutput : Test := do
  let r : Result := { package := "p", moduleName := "M", test := "t", status := .pass }
  let xml := junitReport { results := #[r], seed := 0 }
  assertNotContains "system-out" xml
  assertNotContains "system-err" xml

/-- A test's results are truncated after the cap at quiet verbosity, with a summary, but not at verbose. -/
@[test]
def reportTruncates : Test := do
  let many := (Array.range 60).map fun i =>
    ({ package := "p", moduleName := "M", test := "many", resultPath := #[s!"case {i}"], status := .pass } : Result)
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
    let status : Status := if i == 55 then .fail { message := "boom" } else .pass
    ({ package := "p", moduleName := "M", test := "many", resultPath := #[s!"case {i}"], status } : Result)
  let quiet ← captureOutput do discard <| humanReport .quiet many
  -- The named results have no parent line, so the failure is named in full.
  assertContains "\nFAIL  p/M  many.case 55: boom" quiet.stdout
  assertContains "(... and 9 more passed)" quiet.stdout

/-- `humanReport` returns the number of failures and errors. -/
@[test]
def reportFailureCount : Test := do
  let pass : Result := { package := "p", moduleName := "M", test := "t", status := .pass }
  let fail : Result := { package := "p", moduleName := "M", test := "u", status := .fail { message := "x" } }
  let err : Result := { package := "p", moduleName := "M", test := "v", status := .error "oops" }
  assertBEq 2 (← humanReport .silent #[pass, fail, err])

/-- `markdownReport` gives a tally, an open collapsible per failure, and a per-module table. -/
@[test]
def reportMarkdown : Test := do
  let pass : Result := { package := "p", moduleName := "M", test := "t", status := .pass }
  let f : TestFailure := { message := "boom", detail? := some "expected 1\nactual 2" }
  let fail : Result := { package := "p", moduleName := "M", test := "u", status := .fail f }
  let md := markdownReport { results := #[pass, fail], seed := 0 }
  assertContains "**1** passed · **1** failed" md
  assertContains "<details open><summary>❌ <code>p/M</code> u: boom</summary>" md
  assertContains "expected 1\nactual 2" md
  assertContains "Summary by module" md

/-- `runValue` reports a passing value as passed. -/
@[test]
def runOnePasses : Test := do
  let o ← runValue default (pure () : Test)
  assertBEq "passed" o.status

/-- `runValue` reports a failing value as failed and carries its message. -/
@[test]
def runOneFails : Test := do
  let o ← runValue default (TestResult.fail { message := "boom" })
  assertBEq "failed" o.status
  assertBEq (some "boom") o.message?

/-- A failing run surfaces its captured output in the outcome. -/
@[test]
def runOneCapturesOutput : Test := do
  let o ← runValue default (do IO.println "trace line"; failHere "nope" : Test)
  assertBEq "failed" o.status
  assertBEq 1 o.output.size
  assertBEq "stdout" o.output[0]!.stream
  assertContains "trace line" o.output[0]!.text

/-- An outcome takes the most severe verdict among several named results. -/
@[test]
def runOneAggregates : Test := do
  let o ← runValue default (do result "a" (pure ()); result "b" (failHere "bad") : Test)
  assertBEq "failed" o.status

/-- A passing run still surfaces its captured output. -/
@[test]
def runOnePassOutput : Test := do
  let o ← runValue default (do IO.println "printed"; return true : IO Bool)
  assertBEq "passed" o.status
  assertBEq 1 o.output.size
  assertBEq "stdout" o.output[0]!.stream
  assertContains "printed" o.output[0]!.text

/-- Captured output keeps stdout and stderr distinct and interleaved in order. -/
@[test]
def runOneStreams : Test := do
  let o ← runValue default (do
    IO.println "out one"
    IO.eprintln "err one"
    IO.println "out two"
    return true : IO Bool)
  assertBEq "passed" o.status
  assertBEq 3 o.output.size
  assertBEq "stdout" o.output[0]!.stream
  assertBEq "stderr" o.output[1]!.stream
  assertBEq "stdout" o.output[2]!.stream
/-- `failure` from the `Alternative` instance fails a test. -/
@[test]
def alternativeFailure : Test := expectFail failure

/-- `<|>` recovers from an assertion failure by running the alternative. -/
@[test]
def alternativeOrElse : Test := failure <|> assertBEq 1 1

-- Two guards whose first source line is identical must get distinct generated names.
#test_guard 1 + 1 == 2
#test_guard 1 + 1 == 2
