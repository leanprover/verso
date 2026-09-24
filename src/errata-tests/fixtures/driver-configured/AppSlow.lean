module

public import Errata

open Errata

public section

/-- A test that takes longer than the timeout the driver tests give it. -/
@[test]
def sleeps : Test := IO.sleep 5000

/-- A test whose output comes from a subprocess, which writes to the test executable's own stdout. -/
@[test]
def printsFromSubprocess : Test := do
  let child ← IO.Process.spawn { cmd := "echo", args := #["from a subprocess"] }
  discard child.wait
