/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen

Tests that exercise Errata using Errata itself.
-/
module

public import Errata
public meta import Errata

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

/-- A property test. -/
@[test]
def addComm : Test :=
  property (∀ a b : Nat, a + b = b + a)

open Lean (toJson fromJson?)

deriving instance Plausible.Shrinkable, Plausible.Arbitrary for Position
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

/-- Bytes whose code point is never completed are an error, not silently dropped. -/
@[test]
def captureRejectsDanglingBytes : Test := do
  let results ← resultsOf do
    let out ← IO.getStdout
    out.write ("é".toUTF8.extract 0 1)
  assertEq 1 results.size
  assertTrue (results[0]!.status matches .error _)

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
    writeOutput := fun o => do
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
    writeOutput := fun o => do
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
    writeOutput := fun _ => do
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

/-- The `Verbosity` predicates and accumulation behave as the report relies on. -/
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
  assertEq Verbosity.quiet Verbosity.silent.increase
  assertEq Verbosity.verbose Verbosity.quiet.increase
  assertEq Verbosity.superVerbose Verbosity.verbose.increase
  assertEq Verbosity.superVerbose Verbosity.superVerbose.increase

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
    code.set (← runMain #[] [])
  assertContains "no tests were discovered" out.all
  assertEq 1 (← code.get).toNat

/-- At silent verbosity the report hides passes but shows failures and the summary line. -/
@[test]
def reportSilent : Test := do
  let pass : Result := { package := "p", moduleName := "M", test := "t", status := .pass }
  let fail : Result := { package := "p", moduleName := "M", test := "u", status := .fail { message := "boom" } }
  let out ← captureOutput do discard <| humanReport .silent #[pass, fail]
  assertContains "FAIL  p/M  u: boom" out.stdout
  assertContains "1 passed, 1 failed, 0 errors, 0 skipped" out.stdout
  assertEq 1 (out.stdout.splitOn "ok    ").length

/-- At verbose verbosity the report shows passes too. -/
@[test]
def reportVerbose : Test := do
  let pass : Result := { package := "p", moduleName := "M", test := "t", status := .pass }
  let out ← captureOutput do discard <| humanReport .verbose #[pass]
  assertContains "ok    p/M  t" out.stdout

/-- Characters XML 1.0 forbids are dropped from the JUnit report rather than emitted. -/
@[test]
def junitDropsForbiddenChars : Test := do
  let bad := (Char.ofNat 0xFFFF).toString ++ (Char.ofNat 0xFFFE).toString ++ (Char.ofNat 0x1).toString
  let r : Result := { package := "p", moduleName := "M", test := "t",
                      status := .fail { message := s!"bad{bad}char" } }
  let xml := junitReport #[r]
  assertContains "badchar" xml
  assertTrue (!xml.contains (Char.ofNat 0xFFFF) && !xml.contains (Char.ofNat 0xFFFE))

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
