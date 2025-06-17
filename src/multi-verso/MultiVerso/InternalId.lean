import Lean.Data.Json
import Std.Data.TreeSet

open Lean
open Std

namespace Verso.Multi

/--
An internal identifier assigned to a part during traversal. Users don't get to have influence
over these IDs, so they can be used to ensure uniqueness of tags.

Even though the constructor is private, there is a JSON serialization that can be used to undermine
the uniqueness of internal IDs. Please don't do that - your program may break unpredictably.
-/
structure InternalId where
  private mk ::
  private id : Nat
deriving BEq, Hashable, Repr, Inhabited, Ord

instance : ToJson InternalId where
  toJson | ⟨n⟩ => .num n

instance : FromJson InternalId where
  fromJson? v := do
    return ⟨←  v.getNat?⟩

instance : LT InternalId where
  lt x y := Ord.compare x y = .lt

instance : LE InternalId where
  le x y := x < y ∨ x = y

instance : ToString InternalId where
  toString x := s!"#<{x.id}>"

/--
Returns a fresh ID that's not contained in the provided set of used IDs.
-/
def InternalId.fresh (used : TreeSet InternalId) : InternalId := Id.run do
  let mut i : InternalId := used.max?.map (⟨·.id + 1⟩) |>.getD ⟨0⟩
  while used.contains i do
    i := ⟨i.id + 1⟩
  return i
