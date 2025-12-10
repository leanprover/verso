/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
set_option doc.verso true

/-!
Here is a short demonstration of quotient types, which are used to define a type of sets that are
represented by lists. No requirements are imposed on the type of elements, except for some operators
that require decidable equality.

The demonstration has three parts:
 1. First, an equivalence relation that equates any two lists with the same elements is defined.
 2. Next, various operations on lists are shown to preserve this relation.
 3. Finally, lists are quotiented by the relation, and set operations are defined using list
    operations.

In practice, this is a poor representation, because unsorted linked lists full of duplicates are not
an efficient data structure.
-/

/-!
# The Equivalence Relation
-/

/--
Two lists {name}`xs` and {name}`ys` have the same contents iff any element of one is also an element
of the other.
-/
@[grind]
structure SameContents (xs ys : List α) : Prop where
  inOne : ∀ x ∈ xs, x ∈ ys
  inOther : ∀ y ∈ ys, y ∈ xs

/--
Every list has the same contents as itself. That is, {name}`SameContents` is reflexive.
-/
@[refl]
theorem SameContents.refl (xs : List α) :
    SameContents xs xs := by
  constructor <;> grind

/--
{name}`SameContents` is symmetric.
-/
@[symm, simp, grind .]
theorem SameContents.symm :
    SameContents xs ys → SameContents ys xs := by
  intro ⟨mp, mpr⟩
  constructor <;> assumption

/--
{name}`SameContents` is transitive.
-/
@[simp, grind .]
theorem SameContents.trans :
    SameContents xs ys → SameContents ys zs →
    SameContents xs zs := by
  intro ⟨mp, mpr⟩ ⟨mp', mpr'⟩
  constructor <;> grind

/--
{name}`SameContents` and {lean}`List α` form a setoid.
-/
def SameContents.setoid : Setoid (List α) where
  r := SameContents
  iseqv := ⟨SameContents.refl, SameContents.symm, SameContents.trans⟩

/-!
# List Operators and {name}`SameContents`

Most list operators still make sense if we ignore the order of elements.
-/

/--
If {name}`xs` has the same elements as the empty list, then {name}`xs` is itself empty.
-/
@[simp, grind .]
theorem SameContents.empty : SameContents [] xs → xs = [] := by
  intro ⟨mp, mpr⟩
  cases xs
  . rfl
  . rename_i hd tl
    have := mpr hd
    simp_all

/--
If lists have the same contents, then so do the results of appending them.
-/
@[grind .]
theorem SameContents.append_eq :
    SameContents xs xs' → SameContents ys ys' →
    SameContents (xs ++ ys) (xs' ++ ys') := by
  induction xs <;> grind

/--
If two lists have the same contents, then removing the same elements results in them still having
the same contents.
-/
@[grind .]
theorem SameContents.filter :
    SameContents xs ys →
    SameContents (xs.filter p) (ys.filter p) := by
  intro ⟨_, _⟩
  fun_induction xs.filter p <;> grind

/-!
# The Quotient

{given -show}`α : Type`

Quotienting {lean}`List α` by {name}`SameContents` results in actual finite sets, because ordering
and repetition can no longer be observed.
-/

abbrev ListSet α := Quotient (α := List α) SameContents.setoid

def ListSet.mk (xs : List α) : ListSet α := Quotient.mk _ xs

/-!
## Improving Automation

These helpers allow {tactic}`grind` to translate between the two representations of the setoid that
occur in proofs, so congruence closure can propagate the needed facts. The quotient helpers cause
the simplifier to rewrite many functions into a form where {tactic}`grind` can be used.
-/

@[grind .]
theorem SameContents.setoid_eq_SameContents (xs ys : List α) :
    -- This selects the desired instance over the one
    -- in the standard library
    let _ := setoid (α := α)
    (xs ≈ ys) = SameContents xs ys := by
  simp [HasEquiv.Equiv, setoid]

@[grind .]
theorem ListSet.sound {xs ys : List α} :
    SameContents xs ys →
    ListSet.mk xs = ListSet.mk ys := by
  intro h; exact Quotient.sound h

@[simp, grind =]
theorem Quotient.liftOnBeta
    {x : α} {f : α → β} {p : _} :
    (Quotient.mk s x).liftOn f p = f x := by
  simp [Quotient.mk]

@[simp, grind =]
theorem ListSet.liftOnBeta
    {xs : List α} {f : List α → β} {p : _} :
    (ListSet.mk xs).liftOn f p = f xs := by
  simp [ListSet.mk]

@[simp]
theorem Quotient.liftOn₂beta
    {x : α} {y : β} {f : α → β → γ} {p : _} :
    (Quotient.mk s x).liftOn₂ (Quotient.mk s' y) f p = f x y := by
  simp [Quotient.liftOn₂, Quotient.lift₂, Quotient.lift, Quotient.mk]

@[simp]
theorem ListSet.liftOn₂beta
    {xs : List α} {ys : List β} {f : List α → List β → γ} {p : _} :
    (ListSet.mk xs).liftOn₂ (ListSet.mk ys) f p = f xs ys := by
  simp [ListSet.mk]


/-!
## Defining Set Operators

Finally, basic set operations can be conveniently defined.
-/

/-!

### Membership Test

-/

/--
Checks whether {name}`x` is found in {name}`xs`
-/
def ListSet.contains [DecidableEq α] (xs : ListSet α) (x : α) : Bool :=
  xs.liftOn (fun xs => x ∈ xs) (by intro _ _ ⟨_, _⟩; grind)

/-!
### Insertion
-/

/--
Inserts {name}`x` into {name}`xs`.
-/
def ListSet.insert (xs : ListSet α) (x : α) : ListSet α :=
  xs.liftOn (.mk <| x :: ·) <| by grind

theorem ListSet.insert_contains
    {_ : DecidableEq α} {xs : ListSet α} :
    (xs.insert x).contains x = true := by
  cases xs using Quotient.ind
  simp [insert, contains]

/-!
### Union

Union is implemented by concatenating the underlying lists. This is grossly inefficient, but easy to prove things about.
-/

def ListSet.union (xs ys : ListSet α) : ListSet α :=
  xs.liftOn₂ ys (.mk <| · ++ ·) <| by grind

/--
The following are equivalent:
 * $`x \in A \cup B`
 * $`x \in A \vee x \in B`
-/
theorem ListSet.union_contains
    {_ : DecidableEq α} {xs ys : ListSet α} :
    (xs.union ys).contains x = (xs.contains x ∨ ys.contains x) := by
  cases xs, ys using Quotient.ind₂
  simp [union, contains]

/-!
### Membership

Membership in sets is just membership in the representing list.
-/

def ListSet.Mem (xs : ListSet α) (x : α) : Prop :=
  xs.liftOn (x ∈ ·) <| by grind

instance : Membership α (ListSet α) where
  mem := ListSet.Mem

/--
The containment test is equivalent to the membership predicate.
-/
theorem ListSet.mem_eq_contains
    {_ : DecidableEq α} {xs : ListSet α} :
    xs.contains x = (x ∈ xs) := by
  cases xs using Quotient.ind
  simp [contains, (· ∈ ·), Mem]

/-!
### Subtraction and Intersection

Both operations are implemented using {name}`List.filter`.
-/
def ListSet.minus [DecidableEq α] (xs ys : ListSet α) : ListSet α :=
  xs.liftOn₂ ys (fun xs ys => .mk <| xs.filter (· ∉ ys)) <| by grind

def ListSet.intersection [DecidableEq α] (xs ys : ListSet α) : ListSet α :=
  xs.liftOn₂ ys (fun xs ys => .mk <| xs.filter (· ∈ ys)) <| by grind

theorem ListSet.intersection_commutative
    {_ : DecidableEq α} {xs ys : ListSet α} :
    xs.intersection ys = ys.intersection xs := by
  induction xs, ys using Quotient.ind₂ with
  | h xs ys =>
    simp [intersection]
    grind
