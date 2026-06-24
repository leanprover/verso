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
