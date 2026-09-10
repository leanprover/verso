module

public import Errata

open Errata

/-- A test private to its module, reachable only through `import all`. -/
@[test]
def childTest : Bool := true
