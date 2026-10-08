/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

-- ANCHOR: Tree
inductive Tree (α : Type u) : Type u where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)
-- ANCHOR_END: Tree

-- ANCHOR: Tree.flip
def Tree.flip : Tree α → Tree α
  | .leaf => .leaf
  | .branch l v r =>
-- ANCHOR: flopped
    .branch r.flip v l.flip
-- ANCHOR_END: flopped
-- ANCHOR_END: Tree.flip
