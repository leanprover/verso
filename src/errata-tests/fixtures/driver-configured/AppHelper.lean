module

public import Errata
public import AppHelper.Shout

open Errata

public section

/-- A test that runs a helper from another module in a subprocess of this test executable. -/
@[test]
def runsItsHelper : Test := do
  let out ← runHelper ``AppHelper.shout ["hello", "helper"]
  assertExitCode 7 out
  assertBEq "hello\nhelper\n" out.stdout
