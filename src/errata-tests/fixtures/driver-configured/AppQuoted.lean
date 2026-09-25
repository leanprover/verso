module

public import Errata
public import AppQuoted.«1st»

open Errata

public section

/-- A test in the library's root, beside the module whose name needs quoting. -/
@[test]
def inRoot : Bool := true
