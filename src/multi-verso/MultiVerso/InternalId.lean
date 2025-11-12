/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Lean.Data.Json
public import Std.Data.TreeSet


set_option linter.missingDocs true

open Lean
open Std

namespace Verso.Multi

/--
An internal identifier assigned to a part during traversal. Users don't get to have influence
over these IDs, so they can be used to ensure uniqueness of tags.

Even though the constructor is private, there is a JSON serialization that can be used to undermine
the uniqueness of internal IDs. Please don't do that - your program may break unpredictably.
-/
public structure InternalId where
  private mk ::
  private id : Nat
deriving BEq, DecidableEq, Hashable, Repr, Inhabited, Ord

public instance : ToJson InternalId where
  toJson i := private
    let ⟨n⟩ := i
    .num n

public instance : FromJson InternalId where
  fromJson? v := private do
    return ⟨←  v.getNat?⟩

public instance : LT InternalId where
  lt x y := Ord.compare x y = .lt

public instance : LE InternalId where
  le x y := x < y ∨ x = y

public instance : ToString InternalId where
  toString x := private s!"#<{x.id}>"

/--
Returns a fresh ID that's not contained in the provided set of used IDs along with the updated set.
-/
public def InternalId.fresh (used : TreeSet InternalId) : (InternalId × TreeSet InternalId) := Id.run do
  let mut i : InternalId := used.max?.map (⟨·.id + 1⟩) |>.getD ⟨0⟩
  while used.contains i do
    i := ⟨i.id + 1⟩
  return (i, used.insert i)
