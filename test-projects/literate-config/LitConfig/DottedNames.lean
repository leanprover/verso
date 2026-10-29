/-!
# Dotted Names

A declaration whose name has more than one component keeps its own docstring, separate from the
docstrings of its fields and constructors.
-/

/--
A point whose name has a namespace prefix. Its fields are {name}`Dotted.Geometry.Point.x` and
{name}`Dotted.Geometry.Point.y`.
-/
structure Dotted.Geometry.Point where
  /-- The horizontal coordinate of the point. -/
  x : Nat
  /-- The vertical coordinate of the point. -/
  y : Nat

/--
A class whose name has a namespace prefix. Its field is {name}`Dotted.Algebra.IsReflexive.refl`.
-/
class Dotted.Algebra.IsReflexive (α : Type) : Prop where
  /-- Every element is equal to itself. -/
  refl : ∀ x : α, x = x

/--
A structure whose first field has no docstring. Its constructor is
{name}`Dotted.Geometry.Segment.mk`.
-/
structure Dotted.Geometry.Segment where
  /-- Builds a segment from its endpoints. -/
  mk ::
  start : Dotted.Geometry.Point
  /-- The end of the segment. -/
  stop : Dotted.Geometry.Point

/--
An inductive type whose name has a namespace prefix. Its constructors are {name}`Dotted.Color.red`
and {name}`Dotted.Color.green`.
-/
inductive Dotted.Color where
  /-- The color red. -/
  | red
  /-- The color green. -/
  | green

/--
A class inductive whose name has a namespace prefix. Its constructors are
{name}`Dotted.Algebra.Decision.no` and {name}`Dotted.Algebra.Decision.yes`.
-/
class inductive Dotted.Algebra.Decision (p : Prop) where
  /-- The proposition is false. -/
  | no (h : ¬p)
  /-- The proposition is true. -/
  | yes (h : p)

namespace Dotted

/--
A structure with a dotted name inside a namespace. Its field is {name}`Dotted.Inner.Pair.fst`.
-/
structure Inner.Pair where
  /-- The first component of the pair. -/
  fst : Nat
