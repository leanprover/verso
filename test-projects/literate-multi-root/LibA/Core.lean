/-!
# Core of Library A

Some core definitions for library A.
-/

/-- Doubles a number. -/
def doubleA (n : Nat) : Nat := n * 2

/-- Ignores its argument. `linter.unusedVariables` warns about `ignoreA`. -/
def ignoreA (n : Nat) : Nat := 0
