/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Examples.Basic


-- ANCHOR: t
def t : Tree Nat :=
-- ANCHOR: tDef
  .branch (.branch .leaf 1 .leaf) 2 (.branch (.branch .leaf 3 .leaf) 4 .leaf)
-- ANCHOR_END: tDef
-- ANCHOR_END: t

example := t.flip


-- ANCHOR: tflip
#check Tree.flip
-- ANCHOR_END: tflip




-- ANCHOR: proof1
theorem Tree.flip_flip_id (t : Tree α) : t.flip.flip = t := by
  induction t with
  | leaf => rfl
  | branch l v r ih1 ih2 =>
    simp only [flip]
    rw [ih1]; rw [ih2]
-- ANCHOR_END: proof1

-- ANCHOR: proof2
-- Show more tactic combinators and placement of proof states
theorem Tree.flip_flip_id' (t : Tree α) : t.flip.flip = t := by
  induction t
  case leaf => rfl
  next l v r ih1 ih2 =>
    simp only [flip]
    rw [ih1]; . rw [ih2]
--ANCHOR_END: proof2
