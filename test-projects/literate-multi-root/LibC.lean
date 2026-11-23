module

public import LibC.Core

/-!
# Library C

This library uses the module system, and its root imports a module from the same package.
-/

public section

/-- Triples a number. -/
def tripleC (n : Nat) : Nat := doubleC n + n

end
