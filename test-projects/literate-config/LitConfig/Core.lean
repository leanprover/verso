import LitConfig.Core.Basic

/-!
# Core Module

This is the core module with some basic definitions.
-/

/-!
## Natural Number Utilities
-/

/-- Doubles a natural number. -/
def double (n : Nat) : Nat := n * 2

/-- Triples a natural number. -/
def triple (n : Nat) : Nat := n * 3

/-!
Here are some examples using the {kw}`where` keyword:
-/

#eval double 5
#eval triple 5

/-- An anonymous example docstring. -/
example : 1 + 1 = 2 := rfl
