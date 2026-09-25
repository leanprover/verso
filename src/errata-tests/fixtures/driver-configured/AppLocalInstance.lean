module

public import Errata

open Errata

/-- A verdict type of the module's own. -/
inductive Verdict where
  | good
  | bad

/-- The instance is local, so only this module can run a `Verdict` as a test. -/
local instance : IsTest Verdict where
  toTest
    | .good => pure ()
    | .bad => fail "bad verdict"

/-- A test whose type has an instance only at its declaration. -/
@[test]
def localInstanceTest : Verdict := .good
