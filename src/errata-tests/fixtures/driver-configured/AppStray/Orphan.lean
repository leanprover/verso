module

public import Errata

open Errata

public section

/-- A test in a module that no root reaches, so the driver never discovers it. -/
@[test]
def orphaned : Bool := false
