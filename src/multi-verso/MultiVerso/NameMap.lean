/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lean.Data.Name
import Lean.Data.Json.FromToJson
public import Std.Data.TreeMap

set_option linter.missingDocs true
set_option doc.verso true

namespace Verso
open Std
open Lean

namespace NameMap
/--
Checks whether a name is suitably public to be included in data exported from Verso.

A name is suitably public if it contains at least one string component and no non-string components.
-/
public def isPublic : Name → Bool
  | .str .anonymous _ => true
  | .str y _ => isPublic y
  | _ => false

/--
A name that is suitably public to be included in data exported from Verso.

A name is suitably public if it contains at least one string component and no non-string components.
-/
public abbrev PublicName := { x : Name // isPublic x }

instance : CoeDep Name (.str .anonymous x) PublicName := ⟨⟨.str .anonymous x, by grind [isPublic]⟩⟩

instance [inst : CoeDep Name y PublicName] : CoeDep Name (.str y x) PublicName := ⟨⟨.str inst.coe.val x, by grind [isPublic]⟩⟩

public instance : BEq PublicName where
  beq x y := x.val == y.val

instance : Inhabited PublicName := ⟨ ⟨.str .anonymous "x", by simp [isPublic]⟩⟩

/--
Quickly compares two names. The resulting order is not particularly meaningful for users, but is
useful in data structures.
-/
public def PublicName.quickCmp (x y : PublicName) : Ordering := x.val.quickCmp y.val

/--
Converts a public name to a string.
-/
public def PublicName.toString (x : PublicName) : String :=
  -- This works around the name `.str .anonymous "#"` not round-tripping
  x.val.toStringWithSep "." true (fun _ => true)

/--
Converts a string to a public name, failing with {name}`none` if the string doesn't encode such a name.
-/
public def PublicName.ofString (x : String) : Option PublicName :=
  let name := x.toName
  if h : isPublic name then some ⟨name, h⟩ else none

/--
Converts a string to a public name, failing with {name}`none` if the string doesn't encode such a name.
-/
public def PublicName.ofString! (x : String) : PublicName :=
  let name := x.toName
  if h : isPublic name then ⟨name, h⟩ else panic!"'{name}' is not suitably public to be inserted into a Verso NameMap"


end NameMap

open NameMap

/--
A Verso {name}`NameMap` maps non-empty, string-only names to some kind of value.
-/
public abbrev NameMap (α : Type) : Type :=
  TreeMap PublicName α PublicName.quickCmp

namespace NameMap
variable {α : Type}

public instance [Repr α] : Repr (NameMap α) := inferInstanceAs (Repr (Std.TreeMap _ _ _))

public instance (α : Type) : EmptyCollection (NameMap α) := ⟨{}⟩

public instance (α : Type) : Inhabited (NameMap α) where
  default := {}

@[inherit_doc Std.TreeMap.insert]
public def insert (m : NameMap α) (n : Name) (a : α) (ok : isPublic n := by first | assumption | decide) : NameMap α :=
  Std.TreeMap.insert m ⟨n, ok⟩ a

/--
Inserts a name/value pair into the map. Panics if the name is not suitably public.
-/
public def insert! (m : NameMap α) (n : Name) (a : α) :=
  if h : isPublic n then
    Std.TreeMap.insert m ⟨n, h⟩ a
  else panic! s!"The name `{n}` is not suitably public to be inserted into a Verso `NameMap`"

@[inherit_doc Std.TreeMap.contains]
public def contains (m : NameMap α) (n : Name) : Bool :=
  if h : isPublic n then
    Std.TreeMap.contains m ⟨n, h⟩
  else false

@[inherit_doc Std.TreeMap.get?]
public def get? (m : NameMap α) (n : Name) : Option α :=
  if h : isPublic n then
    Std.TreeMap.get? m ⟨n, h⟩
  else none

@[deprecated get? (since := "2025-11-04"), inherit_doc Std.TreeMap.get?]
public def find? (m : NameMap α) (n : Name) : Option α := get? m n

@[inherit_doc Std.TreeMap.get!]
public def get! [Inhabited α] (m : NameMap α) (n : Name) : α :=
  if h : isPublic n then
    Std.TreeMap.get! m ⟨n, h⟩
  else panic! s!"The name `{n}` is not suitably public to be inserted into a Verso `NameMap`"


public instance : GetElem? (NameMap α) Name α fun xs n => if h : isPublic n then ⟨n, h⟩ ∈ xs else False where
  getElem xs x ok :=
    if h : isPublic x then
      show α from GetElem.getElem (coll := TreeMap PublicName α PublicName.quickCmp ) (valid := fun xs x => x ∈ xs) xs ⟨x, h⟩ <| by
        grind
    else
     False.elim <| by grind
  getElem? xs x := xs.get? x


public instance : ForIn m (NameMap α) (PublicName × α) where
  forIn xs init f := (xs : Std.TreeMap _ _ _).forIn (fun a b acc => f (a, b) acc) init

instance : ForIn m (NameMap α) (Name × α) where
  forIn xs init f := (xs : Std.TreeMap _ _ _).forIn (fun a b acc => f (a.val, b) acc) init

/--
{lean}`filter f m` returns the {name}`NameMap` consisting of all
{given}`key`/{given}`val`-pairs in {name}`m` where {lean}`f key val` returns {lean}`true`.
-/
public def filter (f : Name → α → Bool) (m : NameMap α) : NameMap α :=
  Std.TreeMap.filter (fun x v => f x v) m

end NameMap

section
variable [ToJson α] [FromJson α]

instance : ToJson (NameMap α) where
  toJson v :=
    .obj <| v.foldl (init := {}) fun xs (k : PublicName) (v : α) => xs.insert k.toString (toJson v)

instance : FromJson (NameMap α) where
  fromJson? json := do
    let xs ← json.getObj?
    xs.foldlM (init := {}) fun xs k v => do
      let k' := k.toName
      if h : isPublic k' then
        pure <| xs.insert k' (← fromJson? v) h
      else
        throw s!"Invalid public name `{k'}` (from string {k.quote})"
end
