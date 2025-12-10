/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

set_option doc.verso true

/-!

# Preliminaries

First we define trees.
-/

variable {α : Type u}

/--
Binary trees.
-/
inductive T (α) where
  | leaf : T α
  | branch (left : T α) (val : α) (right : T α) : T α

/-!
## Operations
-/

def T.depth : T α → Nat
  | .leaf => 0
  | .branch l _  r => max l.depth r.depth

/--
Transforms each entry in {name}`t` using {name}`f`.
-/
def T.map (f : α → β) : (t : T α) → T β
  | .leaf => .leaf
  | .branch l x r => .branch (l.map f) (f x) (r.map f)

/--
Depth-first search for {name}`x`
-/
def T.contains [BEq α] (t : T α) (x : α) : Bool :=
  match t with
  | .leaf => false
  | .branch l y r => x == y || l.contains x || r.contains x

/-!
## Construction
-/

/--
The empty tree contains nothing.
-/
def T.empty : T α := .leaf

instance : EmptyCollection (T α) where
  emptyCollection := .leaf

/-!
# Properties
-/



/--
Mapping a function {name}`f` over a tree {name}`t` preserves its depth.
-/
theorem T.map_preserves_depth {t : T α} : (t.map f).depth = t.depth := by
  fun_induction T.map
  . simp [T.depth]
  . simp [T.depth, *]
