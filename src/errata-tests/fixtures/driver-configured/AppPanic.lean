module

public import Errata

open Errata

public section

/-- A test that passes without panicking. -/
@[test]
def calm : Bool := true

/-- A test that panics, which ends its process. -/
@[test]
def panics : Test := do
  let xs : Array Nat := #[]
  -- An index that the compiler cannot fold away.
  let i ← IO.rand 0 0
  assertBEq 0 xs[i]!
