/-!
# Dotted Names

A structure or class whose name has more than one component keeps its own docstring, separate
from the docstrings of its fields.
-/

/-- A point whose name has a namespace prefix. -/
structure Dotted.Geometry.Point where
  /-- The horizontal coordinate of the point. -/
  x : Nat

/-- A class whose name has a namespace prefix. -/
class Dotted.Algebra.IsReflexive (α : Type) : Prop where
  /-- Every element is equal to itself. -/
  refl : ∀ x : α, x = x
