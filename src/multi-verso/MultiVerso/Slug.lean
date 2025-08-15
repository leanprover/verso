/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Std.Data.HashSet
import Verso.Method

set_option linter.missingDocs true

namespace Verso.Multi
open Verso.Method
open Lean (ToJson FromJson)
open Std (HashSet)

private def validCharString := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_"


/-- The characters allowed in slugs. -/
def Slug.validChars := HashSet.ofList validCharString.toList

/--
A slug is well-formed if all its characters are valid.
-/
def Slug.WF (str : String) : Prop :=
  str.toList.all (· ∈ validChars)

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let mut iter := validCharString.iter
  while h : iter.hasNext do
    let c := iter.curr' h
    iter := iter.next' h
    let n := mkIdent <| `Slug ++ (.str .anonymous s!"'{c}'_mem_validChars")
    let cmd ←
      `(@[simp, grind] protected theorem $n : ($(quote c) ∈ Slug.validChars) := by simp [Slug.validChars, validCharString])
    elabCommand cmd


private def mangle (c : Char) : String :=
  replacements.lookup c |>.getD "___"
where
  replacements : List (Char × String) := [
    ('<', "_LT_"),
    ('>', "_GT_"),
    (';', "_SEMI_"),
    ('‹', "_FLQ_"),
    ('›', "_FRQ_"),
    ('«', "_FLQQ_"),
    ('»', "_FLQQ_"),
    ('⟨', "_LANGLE_"),
    ('⟩', "_RANGLE_"),
    ('(', "_LPAR_"),
    (')', "_RPAR_"),
    ('[', "_LSQ_"),
    (']', "_RSQ_"),
    ('→', "_ARR_"),
    ('↦', "_MAPSTO_"),
    ('⊢', "_VDASH_")
  ]


@[simp, grind] theorem mangle.replacements_all_wf : (k, v) ∈ mangle.replacements → Slug.WF v := by
  simp [Slug.WF, replacements]
  intro
  repeat (rename_i hk; cases hk; simp [*])

@[simp, grind]
private theorem mangle.replacements_wf (c : Char) : (c, s) ∈ mangle.replacements → Slug.WF (mangle c) := by
  unfold mangle
  generalize h : mangle.replacements = reps
  have : ∀ k v, (k, v) ∈ reps → Slug.WF v := by
    rw [← h]
    grind only [=_ List.contains_iff_mem, mangle.replacements_all_wf]
  clear h
  fun_induction List.lookup <;> first | grind | simp

@[simp, grind]
private theorem mangle_wf (c : Char) : Slug.WF (mangle c) := by
  unfold mangle
  by_cases h : ∃ s, (c, s) ∈ mangle.replacements
  . let ⟨w, p⟩ := h
    apply mangle.replacements_wf _ p
  . suffices List.lookup c mangle.replacements = none by
      rw [this]
      simp [Slug.WF]
    generalize h' : mangle.replacements = xs
    rw [h'] at h
    clear h'
    fun_induction List.lookup with try ((first | grind | simp); done)

@[simp, grind]
private theorem mangle_mem_valid (c : Char) : c ∈ (mangle c').data → c ∈ Slug.validChars := by
  intro mem
  have := mangle_wf c'
  simp [Slug.WF] at this
  apply this
  assumption

/--
Converts a string to a valid slug, mangling as appropriate.
-/
def asSlug (str : String) : String :=
  let rec loop (iter : String.Iterator) (acc : String) : String :=
    if iter.atEnd then acc
    else
      let c := iter.curr
      loop iter.next <|
        if c ∈ Slug.validChars then acc.push c
        else if c.isWhitespace then acc.push '-'
        else acc ++ mangle c
  loop str.iter ""

instance : Decidable (c ∈ Slug.validChars) := inferInstance

instance [DecidablePred p] : Decidable (String.all s (p ·)) :=
  if h : String.all s (p ·) then
    isTrue h
  else
    isFalse h

@[simp]
theorem String.empty_all_eq_true : "".all p = true := by
  simp [String.all, String.any, String.endPos, String.utf8ByteSize, String.utf8ByteSize.go, String.anyAux]

@[simp]
theorem String.Pos.add_0_eq_size {c : Char} : (0 : String.Pos) + c = ⟨c.utf8Size⟩ := by
  simp only [HAdd.hAdd, String.Pos.byteIdx_zero, String.Pos.mk.injEq]
  grind

instance : DecidablePred Slug.WF := fun str =>
  if h : str.toList.all (· ∈ Slug.validChars) then
    isTrue h
  else
    isFalse h

@[grind]
theorem Slug.wf_push (c str) : c ∈ validChars → WF str → WF (str.push c) := by
  unfold WF
  cases str
  intro mem wf
  simp only [String.toList, List.all_eq_true, decide_eq_true_eq] at wf
  simp only [String.toList, String.data_push, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  grind only

@[grind]
theorem Slug.wf_append (str1 str2) : WF str1 → WF str2 → WF (str1 ++ str2) := by
  unfold WF
  cases str1; cases str2
  intro wf1 wf2
  simp only [String.toList, String.data_append, List.all_append, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  simp only [String.toList, List.all_eq_true, decide_eq_true_eq] at wf1 wf2
  grind only

@[simp]
theorem Slug.decide_WF_eq_wf (s : String) : (s.toList.all (fun x => decide (x ∈ validChars)) = true) = WF s := by
  rfl

@[grind, simp]
theorem Slug.wf_forall : WF s → c ∈ s.data → c ∈ validChars := by
  intro wf h
  simp_all [WF]

theorem Slug.asSlug_loop_valid : WF acc → WF (asSlug.loop iter acc) := by
  intro wfAcc
  fun_induction asSlug.loop with try assumption
  | case2 iter acc notEnd c ih =>
    apply ih
    unfold WF
    (repeat' split) <;>
      simp [*] <;>
      grind only [=_ List.contains_iff_mem, List.contains_eq_mem, mangle_wf, wf_forall, mangle_mem_valid, wf_append, cases Or]

@[grind]
theorem Slug.asSlug_valid : WF (asSlug str) := by
  unfold asSlug
  apply asSlug_loop_valid
  simp [WF]

/--
A slug is a well-formed string.
-/
structure Slug where
  private mk ::
  /-- Converts the slug to the underlying string. -/
  toString : String
  /-- The underlying string is well-formed. -/
  wf : Slug.WF toString
deriving BEq, Hashable, DecidableEq, Ord, Repr

instance : ToString Slug := ⟨Slug.toString⟩

instance : ToJson Slug where
  toJson | ⟨str, _⟩ => ToJson.toJson str

instance : FromJson Slug where
  fromJson? v := do
    let s : String ← FromJson.fromJson? v
    if h : asSlug s = s then pure ⟨s, h ▸ Slug.asSlug_valid⟩
    else throw s!"String {s} contains invalid characters"

namespace Slug

instance : LT Slug where
  lt := (·.toString < ·.toString)

instance : DecidableRel (@LT.lt Slug _) := fun s1 s2 =>
  if h : s1.toString < s2.toString then .isTrue h else .isFalse h

instance : LE Slug where
  le s1 s2 := s1 = s2 ∨ s1 < s2

instance : DecidableRel (@LE.le Slug _) := fun s1 s2 =>
  if h : s1 = s2 then .isTrue (.inl h)
  else if h' : s1.toString < s2.toString then .isTrue (.inr h')
  else .isFalse <| by intro nope; cases nope <;> contradiction

defmethod String.sluggify (str : String) : Slug :=
  ⟨asSlug str, asSlug_valid⟩

/--
Converts a string to a slug.
-/
def ofString (str : String) : Slug := str.sluggify

/--
Returns a slug that's not present in `used`, starting with `slug` and appending consecutive numbers
until it becomes unique.

The consecutive numbers start at `startCount`, which is `1` by default. Callers with reason to
believe that there will be many collisions may provide an alternative starting value.
-/
partial def unique (used : HashSet Slug) (slug : Slug) (startCount : Nat := 1) : Slug :=
  if !(used.contains slug) then slug
  else
    let rec attempt (i : Nat) :=
      let slug' := s!"{slug.toString}{i}".sluggify
      if !(used.contains slug') then slug'
      else attempt (i + 1)
    attempt startCount
