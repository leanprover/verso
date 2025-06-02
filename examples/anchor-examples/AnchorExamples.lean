/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import AnchorExamples.Basic


-- ANCHOR: t
def someTree : Tree Nat :=
-- ANCHOR: tDef
  .branch (.branch .leaf 1 .leaf) 2 (.branch (.branch .leaf 3 .leaf) 4 .leaf)
-- ANCHOR_END: tDef
-- ANCHOR_END: t

example := someTree.flip

deriving instance Repr for Tree

-- ANCHOR: tflip
#eval someTree.flip
-- ANCHOR_END: tflip




-- ANCHOR: proof1
theorem Tree.flip_flip_eq_id : flip ∘ flip = (id : Tree α → Tree α) := by
  funext t
  induction t with
  | leaf => rfl
-- ANCHOR: proof1a
  | branch l v r ih1 ih2 =>
    simp_all [flip]
-- ANCHOR_END: proof1a
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
