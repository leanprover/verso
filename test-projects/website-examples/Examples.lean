/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Examples.Basic

deriving instance Repr for Tree

-- ANCHOR: basic
def t : Tree Nat := .branch (.branch .leaf 1 .leaf) 2 (.branch (.branch .leaf 3 .leaf) 4 .leaf)

example := t.flip

#eval t.flip

#check Tree.flip
-- ANCHOR_END: basic

-- ANCHOR: proof
theorem Tree.flip_flip_id (t : Tree α) : t.flip.flip = t := by
  induction t with
  | leaf => rfl
  | branch l v r ih1 ih2 =>
    simp only [flip]
    rw [ih1]; rw [ih2]

-- Show more tactic combinators and placement of proof states
theorem Tree.flip_flip_id' (t : Tree α) : t.flip.flip = t := by
  induction t
  case leaf => rfl
  next l v r ih1 ih2 =>
    simp only [flip]
    rw [ih1]; . rw [ih2]
-- ANCHOR_END: proof

-- ANCHOR: oldterm
-- The old syntax:
def foo (n k : Nat) : Nat :=
  if n < k then
    1 + foo (n + 1) k
  else 0
termination_by k - n
-- ANCHOR_END: oldterm

-- ANCHOR: version
#eval Lean.versionString
-- ANCHOR_END: version

-- ANCHOR: natRec
example : Nat := Nat.rec 3 (fun _ n => n + 1) 2
-- ANCHOR_END: natRec
