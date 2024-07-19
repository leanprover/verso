/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Std.Data.HashSet
import Verso.Method

namespace Verso.Genre.Manual
open Verso.Method
open Lean (ToJson FromJson)
open Std (HashSet)

def Slug.validChars := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-".toList


def asSlug (str : String) : String :=
  let rec loop (iter : String.Iterator) (acc : String) : String :=
    if iter.atEnd then acc
    else
      let c := iter.curr
      loop iter.next <|
        if c ∈ Slug.validChars then acc.push c
        else if c.isWhitespace then acc.push '-'
        else acc
  loop str.iter ""

def Slug.WF (str : String) : Prop := ∀ c, c ∈ str.data → c ∈ validChars

theorem Slug.wf_push (c str) : c ∈ validChars → WF str → WF (str.push c) := by
  unfold WF
  intro _ wf _ mem
  simp only [String.data_push, List.mem_append, List.mem_singleton] at mem
  cases mem
  . apply wf; assumption
  . simp [*]

theorem Slug.asSlug_loop_valid : WF acc → WF (asSlug.loop iter acc) := by
  intro wfAcc
  induction iter, acc using asSlug.loop.induct <;> unfold asSlug.loop <;> simp [*]
  case case2 iter acc notEnd c ih =>
    apply ih
    unfold WF
    intro c'
    unfold WF at wfAcc
    split
    . simp; intro h; cases h
      . apply wfAcc; assumption
      . simp [*]
    . split
      . intro inPushDash
        simp at inPushDash
        cases inPushDash
        . simp [*]
        . simp [*, validChars]
      . apply wfAcc

theorem Slug.asSlug_valid : WF (asSlug str) := by
  unfold asSlug
  apply asSlug_loop_valid
  unfold WF; intro c h; cases h

structure Slug where
  private mk ::
  toString : String
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

def ofString (str : String) : Slug := str.sluggify

partial def unique (used : HashSet Slug) (slug : Slug) : Slug :=
  if !(used.contains slug) then slug
  else
    let rec attempt (i : Nat) :=
      let slug' := s!"{slug.toString}{i}".sluggify
      if !(used.contains slug') then slug'
      else attempt (i + 1)
    attempt 1
