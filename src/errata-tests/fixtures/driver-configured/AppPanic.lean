module

public import Errata

open Errata

/-- A test that passes without panicking. -/
@[test]
def calm : Bool := true

/-- A test that panics and still passes, since a panic returns a default value. -/
@[test]
def panicsThenPasses : Test := do
  let xs : Array Nat := #[]
  -- An index that the compiler cannot fold away.
  let i ← IO.rand 0 0
  assertEq 0 xs[i]!
