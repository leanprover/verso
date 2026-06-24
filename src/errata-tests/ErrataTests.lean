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
def equality : TestM Unit := do
  assertEq 4 (2 + 2)

/-- A test with named results. -/
@[test]
def named : TestM Unit := do
  result "first" (assertEq 1 1)
  result "second" (assertContains "b" "abc")

/-- A test that completes without any check is a bare success. -/
@[test]
def emptyBody : TestM Unit := pure ()

/-- A test that expects a failure. -/
@[test]
def expectsFailure : TestM Unit :=
  expectFail (assertEq 1 2)

/-- A data-driven family expressed as a plain loop. -/
@[test]
def squares : TestM Unit := do
  for (n, sq) in [(1, 1), (2, 4), (3, 9)] do
    result s!"square {n}" (assertEq sq (n * n))

/-- A subprocess test. -/
@[test]
def echoRuns : TestM Unit := do
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

/-- A property test. -/
@[test]
def addComm : TestM Unit :=
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
def jsonRoundTrips : TestM Unit :=
  property (∀ r : Result, (fromJson? (toJson r)).toOption = some r)

/-- A temp-directory fixture with a golden file. -/
@[test]
def goldenRoundTrip : TestM Unit :=
  IO.FS.withTempDir fun dir => do
    let cfg ← read
    -- In update mode this would write; here we drive it through a temp golden file.
    let goldenPath := dir / "expected.txt"
    IO.FS.writeFile goldenPath "contents\n"
    assertFileExists goldenPath
    let _ := cfg
    goldenFile goldenPath "contents\n"

/-- The `Verbosity` predicates and accumulation behave as the report relies on. -/
@[test]
def verbosityLevels : TestM Unit := do
  assertEq false Verbosity.silent.showsPasses
  assertEq true Verbosity.quiet.showsPasses
  assertEq true Verbosity.verbose.showsPasses
  assertEq false Verbosity.silent.truncates
  assertEq true Verbosity.quiet.truncates
  assertEq false Verbosity.verbose.truncates
  assertEq Verbosity.quiet Verbosity.silent.increase
  assertEq Verbosity.verbose Verbosity.quiet.increase
  assertEq Verbosity.verbose Verbosity.verbose.increase

/-- At silent verbosity the report hides passes but shows failures and the summary line. -/
@[test]
def reportSilent : TestM Unit := do
  let pass : Result := { package := "p", moduleName := "M", test := "t", status := .pass }
  let fail : Result := { package := "p", moduleName := "M", test := "u", status := .fail { message := "boom" } }
  let out ← captureOutput do discard <| humanReport .silent #[pass, fail]
  assertContains "FAIL  p/M  u: boom" out.stdout
  assertContains "1 passed, 1 failed, 0 errored, 0 skipped" out.stdout
  assertEq 1 (out.stdout.splitOn "ok    ").length

/-- At verbose verbosity the report shows passes too. -/
@[test]
def reportVerbose : TestM Unit := do
  let pass : Result := { package := "p", moduleName := "M", test := "t", status := .pass }
  let out ← captureOutput do discard <| humanReport .verbose #[pass]
  assertContains "ok    p/M  t" out.stdout

/-- A test's results are truncated after the cap at quiet verbosity, with a summary, but not at verbose. -/
@[test]
def reportTruncates : TestM Unit := do
  let many := (Array.range 60).map fun i =>
    ({ package := "p", moduleName := "M", test := "many", resultPath := #[s!"case {i}"], status := .pass } : Result)
  let quiet ← captureOutput do discard <| humanReport .quiet many
  assertEq 51 (quiet.stdout.splitOn "ok    ").length
  assertContains "(... and 10 more passed, 0 more failed)" quiet.stdout
  let verbose ← captureOutput do discard <| humanReport .verbose many
  assertEq 61 (verbose.stdout.splitOn "ok    ").length
  assertEq 1 (verbose.stdout.splitOn "(... and").length

/-- `humanReport` returns the number of failures and errors. -/
@[test]
def reportFailureCount : TestM Unit := do
  let pass : Result := { package := "p", moduleName := "M", test := "t", status := .pass }
  let fail : Result := { package := "p", moduleName := "M", test := "u", status := .fail { message := "x" } }
  let err : Result := { package := "p", moduleName := "M", test := "v", status := .error "oops" }
  assertEq 2 (← humanReport .silent #[pass, fail, err])
