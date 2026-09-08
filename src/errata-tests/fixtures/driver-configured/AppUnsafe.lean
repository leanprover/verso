module

public import Errata

open Errata

/-- A safe test beside the unsafe one. -/
@[test]
def alsoSafe : Bool := true

/-- An unsafe test, which makes the generated runner unsafe. -/
@[test]
unsafe def unsafeTest : Bool := unsafeCast (1 : Nat) == (1 : Nat)
