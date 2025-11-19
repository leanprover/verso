/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lean.Data.Name
import Lean.Data.Json.FromToJson
public import Lean.Data.Json.FromToJson.Basic
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
public structure PublicName where
  /--
  Converts a public name to a name, forgetting the proof that the name is suitably public.
  -/
  toName : Name
  toName_isPublic : isPublic toName := by first | decide | grind
deriving Repr

namespace PublicName

attribute [grind =] PublicName.toName_isPublic

@[grind =]
public theorem isPublic_singleton : isPublic (.str .anonymous s) := by
  simp [isPublic]

@[grind =]
public theorem isPublic_str : isPublic x → isPublic (.str x s) := by
  intro h
  unfold isPublic <;> split <;> simp_all

@[grind .]
public theorem not_isPublic_num : ¬isPublic (.num x n) := by simp [isPublic]

@[grind ., simp]
public theorem not_isPublic_anonymous : ¬isPublic .anonymous := by simp [isPublic]

@[grind .]
public theorem not_isPublic_anonymous' : isPublic x → x ≠ .anonymous := by
  intro h; cases x <;> simp_all

public theorem not_isPublic_fallback :
    (∀ (s : String), x ≠ .str .anonymous s) →
    (∀ (y : Name) (str : String), x ≠ y.str str) →
    ¬isPublic x := by
  cases x <;> simp [isPublic]

@[grind →, simp]
public theorem isPublic_str_prefix : isPublic (.str x s) → x = .anonymous ∨ isPublic x := by
  intro h
  cases x with
  | anonymous => simp
  | num => contradiction
  | str =>
    simp only [isPublic] at h
    simp [*]

@[simp]
public theorem isPublic_str_prefix' : (isPublic (.str x s)) = (x = .anonymous ∨ isPublic x) := by
  apply propext
  constructor
  . apply isPublic_str_prefix
  . intro h
    cases h <;>
    unfold isPublic <;>
    split <;> simp_all

/--
Converts a name to a suitably-public name.
-/
public def ofName (x : Name) (x_isPublic : isPublic x := by first | decide | grind) : PublicName := PublicName.mk x x_isPublic

end PublicName

public instance : Coe PublicName Name where
  coe x := x.toName

instance : CoeDep Name (.str .anonymous x) PublicName := ⟨⟨.str .anonymous x, by grind⟩⟩

instance [inst : CoeDep Name y PublicName] : CoeDep Name (.str y x) PublicName where
  coe := .ofName (.str inst.coe.toName x) <| by
    unfold CoeDep.coe;
    cases inst; cases ‹PublicName›
    simp [*]

public instance : BEq PublicName where
  beq x y := x.toName == y.toName

public instance : Hashable PublicName where
  hash | ⟨x, _⟩ => hash x

public instance : Inhabited PublicName := ⟨ ⟨.str .anonymous "x", by simp [isPublic]⟩⟩

/--
Quickly compares two names. The resulting order is not particularly meaningful for users, but is
useful in data structures.
-/
public def PublicName.quickCmp (x y : PublicName) : Ordering := x.toName.quickCmp y.toName

/--
Converts a public name to a string.
-/
public def PublicName.toString (x : PublicName) : String :=
  -- This works around the name `.str .anonymous "#"` not round-tripping
  x.toName.toStringWithSep "." true (fun _ => false)

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
@[expose]
public def NameMap (α : Type) : Type :=
  TreeMap PublicName α PublicName.quickCmp

namespace NameMap
variable {α : Type}

public instance [Repr α] : Repr (NameMap α) := inferInstanceAs (Repr (Std.TreeMap PublicName α PublicName.quickCmp))

public instance (α : Type) : EmptyCollection (NameMap α) := ⟨({} : TreeMap PublicName α PublicName.quickCmp)⟩

public instance (α : Type) : Inhabited (NameMap α) where
  default := {}

@[inherit_doc Std.TreeMap.insert]
public def insert (m : NameMap α) (n : Name) (a : α) (ok : isPublic n := by first | decide | grind) : NameMap α :=
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

public instance {α} : Membership Name (NameMap α) where
  mem xs n :=
    if h : isPublic n then
      let x : PublicName := ⟨n, h⟩
      let xs : TreeMap PublicName α PublicName.quickCmp := xs
      x ∈ xs
    else False

public instance : GetElem? (NameMap α) Name α fun xs n => n ∈ xs where
  getElem xs x ok :=
    if h : isPublic x then
      show α from GetElem.getElem (coll := TreeMap PublicName α PublicName.quickCmp) (idx := PublicName) (elem := α) (valid := fun xs x => x ∈ xs) xs ⟨x, h⟩ <| by
        simp only [Membership.mem, h, dite_cond_eq_true] at ok
        exact ok
    else
     False.elim <| by
       simp only [Membership.mem, h] at ok
       exact ok
  getElem? xs x := xs.get? x


public instance : ForIn m (NameMap α) (PublicName × α) where
  forIn xs init f := (xs : Std.TreeMap _ _ _).forIn (fun a b acc => f (a, b) acc) init

instance : ForIn m (NameMap α) (Name × α) where
  forIn xs init f := (xs : Std.TreeMap _ _ _).forIn (fun a b acc => f (a.toName, b) acc) init

/--
{lean}`filter f m` returns the {name}`NameMap` consisting of all
{given}`key`/{given}`val`-pairs in {name}`m` where {lean}`f key val` returns {lean}`true`.
-/
public def filter (f : Name → α → Bool) (m : NameMap α) : NameMap α :=
  Std.TreeMap.filter (fun x v => f x v) m



section
variable [ToJson α] [FromJson α]

public instance : ToJson (NameMap α) where
  toJson v := private
    .obj <| v.foldl (init := {}) fun xs (k : PublicName) (v : α) => xs.insert k.toString (toJson v)

public instance : FromJson (NameMap α) where
  fromJson? json := private do
    let xs ← json.getObj?
    xs.foldlM (init := {}) fun xs k v => do
      let k' := k.toName
      if h : isPublic k' then
        pure <| xs.insert k' (← fromJson? v) h
      else
        throw s!"Invalid public name `{k'}` (from string {k.quote})"
end
