/-!
# Utilities for Library B

Some utility definitions for library B.
-/

/-- Triples a number. -/
def tripleB (n : Nat) : Nat := n * 3

/--
Ignores its argument. The library options for `LibB` disable the `unusedVariables` linter with a
`weak.` option, so `ignoreB` should have no warning.
-/
def ignoreB (n : Nat) : Nat := 0
