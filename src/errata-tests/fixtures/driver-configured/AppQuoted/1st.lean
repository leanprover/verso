module

public import Errata

open Errata

public section

/-- A test in a module whose name begins with a digit, so Lean writes it as `AppQuoted.«1st»`. -/
@[test]
def inQuoted : Bool := true
