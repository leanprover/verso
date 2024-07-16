/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Method

namespace Verso.Genre.Manual
open Verso.Method

structure Slug where
  toString : String
deriving BEq, Hashable, DecidableEq, Ord

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

instance : Coe String Slug where
  coe := (⟨·⟩)


defmethod String.sluggify (str : String) : Slug := Id.run do
  let mut s := ""
  for c in str.data do
    if c.isAlpha then
      s := s.push c.toLower
    else if c.isDigit then
      s := s.push c
    else if c == ' ' || c == '-' then
      s := s.push '-'
  ⟨s⟩

partial def unique (used : Lean.HashSet Slug) (slug : Slug) : Slug :=
  if !(used.contains slug) then slug
  else
    let rec attempt (i : Nat) :=
      let slug' := s!"{slug.toString}{i}"
      if !(used.contains slug') then slug'
      else attempt (i + 1)
    attempt 1
