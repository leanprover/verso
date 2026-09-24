module

public import Errata

open Errata

public section

/-- A grade type of the module's own. -/
inductive Grade where
  | good
  | bad

/-- The instance is local, so only this module can run a `Grade` as a test. -/
local instance : IsTest Grade where
  toTest
    | .good => pure ()
    | .bad => fail "bad grade"

/-- A test whose type has an instance only at its declaration. -/
@[test]
def localInstanceTest : Grade := .good
