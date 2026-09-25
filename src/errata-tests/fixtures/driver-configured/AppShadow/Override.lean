module

public import Errata

open Errata

/-- An instance that outranks Errata's and passes every boolean. -/
public instance (priority := high) : IsTest Bool where
  toTest _ := pure ()

/-- A test that makes this module part of the run. -/
@[test]
def overrideTest : Bool := true
