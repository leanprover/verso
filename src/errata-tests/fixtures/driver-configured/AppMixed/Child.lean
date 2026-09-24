module

public import Errata

open Errata

public section

/-- A module-system test, imported by a root without a `module` header. -/
@[test]
def childTest : Bool := true
