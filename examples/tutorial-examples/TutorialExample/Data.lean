/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoTutorial

open Verso.Genre
open Verso.Genre.Manual.InlineLean

#doc (Tutorial) "Inductive Types" =>
%%%
slug := "inductive-types"
summary := "describes inductive types"
exampleStyle := .inlineLean `Data
%%%


This is a machine-generated tutorial for use in testing the tutorials feature.
Please don't attempt to actually learn from it!
Think of it as more-realistic Lorem Ipsum.

# Basic Inductive Data Types

## Simple Enumerations

The simplest inductive types enumerate a finite set of constructors:

```lean
inductive Color where
  | red
  | green
  | blue

-- Using the type
def favoriteColor : Color := Color.red

def colorToString (c : Color) : String :=
  match c with
  | Color.red => "red"
  | Color.green => "green"
  | Color.blue => "blue"
```

## Recursive Data Types: Natural Numbers

Natural numbers demonstrate recursion in inductive types:

```lean
inductive Natural where
  | zero : Natural
  | succ : Natural → Natural

-- Examples
def three : Natural := .succ (.succ (.succ .zero))

def add : Natural → Natural → Natural
  | .zero, n => n
  | .succ m, n => .succ (add m n)

def mult : Natural → Natural → Natural
  | .zero, _ => .zero
  | .succ m, n => add n (mult m n)
```

## Lists

Lists are a fundamental polymorphic inductive type:

```lean
inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

-- Notation often used: [] for nil, :: for cons
-- [1, 2, 3] desugars to cons 1 (cons 2 (cons 3 nil))

def length {α : Type} : MyList α → Nat
  | .nil => 0
  | .cons _ tail => 1 + length tail

def append {α : Type} : MyList α → MyList α → MyList α
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (append xs ys)

def map {α β : Type} (f : α → β) : MyList α → MyList β
  | .nil => .nil
  | .cons x xs => .cons (f x) (map f xs)
```

## Binary Trees

Trees demonstrate nested recursion:

```lean
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : α → Tree α → Tree α → Tree α

def treeSize {α : Type} : Tree α → Nat
  | Tree.leaf =>
    0
  | Tree.node _ left right =>
    1 + treeSize left + treeSize right

def treeMap {α β : Type} (f : α → β) : Tree α → Tree β
  | Tree.leaf => Tree.leaf
  | Tree.node x left right =>
      Tree.node (f x) (treeMap f left) (treeMap f right)

-- Example tree
def exampleTree : Tree Nat :=
  Tree.node 5
    (Tree.node 3 Tree.leaf Tree.leaf)
    (Tree.node 7 Tree.leaf Tree.leaf)
```

## Rose Trees (Variable Branching)

Rose trees use lists for arbitrary branching:

```lean
inductive RoseTree (α : Type) where
  | node : α → List (RoseTree α) → RoseTree α

def roseTreeSize {α : Type} : RoseTree α → Nat
  | RoseTree.node _ children =>
      1 + (children.map roseTreeSize).sum
```

# Dependently-Typed Inductive Types

Dependently-typed inductive types have indices that can vary in their constructors, enabling types to encode invariants.

## Length-Indexed Vectors

Vectors are lists with their length encoded in the type:

```lean
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

-- The type checker knows the length
def head {α : Type} {n : Nat} : Vec α (n + 1) → α
  | Vec.cons x _ => x

def tail {α : Type} {n : Nat} : Vec α (n + 1) → Vec α n
  | Vec.cons _ xs => xs

-- Append: types guarantee correct length
def vecAppend :
    Vec α m → Vec α n → Vec α (m + n)
  | .nil, ys =>
    (show n = 0 + n by grind) ▸ ys
  | .cons (n:=n') x xs, ys =>
    let tail := vecAppend xs ys
    (show n' + n + 1 = n' + 1 + n by clear tail; grind) ▸
    .cons x tail

-- Zip: only type-checks when lengths match
def zipWith {α β γ : Type} {n : Nat}
    (f : α → β → γ) : Vec α n → Vec β n → Vec γ n
  | Vec.nil, Vec.nil =>
    Vec.nil
  | Vec.cons x xs, Vec.cons y ys =>
    Vec.cons (f x y) (zipWith f xs ys)
```

## Finite Sets

The type `Finite n` represents natural numbers less than `n`:

```lean
inductive Finite : Nat  → Type where
  | zero : Finite (n + 1)
  | succ : Finite n → Finite (n + 1)

-- Safe indexing into vectors
def vecGet : Vec α n → Finite n → α
  | Vec.cons x _, .zero => x
  | Vec.cons _ xs, .succ i => vecGet xs i

-- Example: Fin 3 has exactly three inhabitants
def allFin3 : List (Finite 3) :=
  [.zero, .succ .zero, .succ (.succ .zero)]
```

## Equality Type

The equality type is built into Lean but can be defined as:

```lean
inductive Eq' {α : Type u} (x : α) : α → Prop where
  | refl : Eq' x x

-- Notation: a = b is sugar for Eq a b
```

# Inductive Predicates

Inductive predicates define properties or relations inductively. They live in `Prop` rather than `Type`.

## Even Numbers

A predicate for even natural numbers:

```lean
inductive Even : Nat → Prop where
  | zero : Even 0
  | succ : Even n → Even (n + 2)

-- Proofs
example : Even 4 :=
  Even.succ (Even.succ Even.zero)

-- We can prove properties
theorem even_plus_even :
    Even m → Even n → Even (m + n) := by
  intro hm hn
  induction hm with
  | zero => simp_all
  | succ k ih =>
    rename_i j
    grind [Even.succ]
```

## Less Than or Equal

The less-than-or-equal relation:

```lean
inductive LessOrEq : Nat → Nat → Prop where
  | refl : LessOrEq n n
  | step : LessOrEq m n → LessOrEq m (n + 1)

-- Notation: m ≤ n

example : LessOrEq 2 5 :=
  .step (.step (.step .refl))

theorem le_trans :
    LessOrEq a b → LessOrEq b c → LessOrEq a c := by
  intro hab hbc
  induction hbc with
  | refl => exact hab
  | step _ ih => exact LessOrEq.step ih
```

## MyList Membership

Membership in a List as an inductive predicate:

```lean
inductive ListMem {α : Type} : α → List α → Prop where
  | head : ListMem x (x :: xs)
  | tail : ListMem x xs → ListMem x (y :: xs)

-- Notation: x ∈ xs

example : ListMem 2 [1, 2, 3] :=
  .tail .head

theorem mem_append_left :
    ListMem x xs → ListMem x (xs ++ ys) := by
  intro h
  induction h with
  | head => exact .head
  | tail _ ih => exact .tail ih
```

## Sorted Lists

A predicate for sorted lists:

```lean
inductive Sorted : List Nat → Prop where
  | nil : Sorted []
  | single : Sorted [x]
  | cons : x ≤ y → Sorted (y :: ys) → Sorted (x :: y :: ys)

example : Sorted [1, 3, 5, 7] :=
  Sorted.cons (by decide)
    (Sorted.cons (by decide)
      (Sorted.cons (by decide)
        Sorted.single))
```

## Reflexive Transitive Closure

The reflexive transitive closure of a relation:

```lean
inductive RTC {α : Type} (R : α → α → Prop) :
    α → α → Prop where
  | refl : RTC R x x
  | step : R x y → RTC R y z → RTC R x z

-- Example: steps in a state machine
inductive Step : Nat → Nat → Prop where
  | incr : Step n (n + 1)
  | double : Step n (2 * n)

-- Can reach 8 from 1
example : RTC Step 1 8 :=
  RTC.step Step.incr
    (RTC.step Step.double
      (RTC.step Step.double
        RTC.refl))
```

## SubList Relation

One List is a SubList of another:

```lean
inductive SubList {α : Type} : List α → List α → Prop where
  | nil : SubList [] ys
  | cons : SubList xs ys → SubList xs (y :: ys)
  | cons₂ : SubList xs ys → SubList (x :: xs) (x :: ys)

example : SubList [1, 3] [1, 2, 3, 4] :=
  .cons₂ (.cons (.cons₂ .nil))
```

#. Advanced Topics

## Mutually Inductive Types

Types can be defined mutually recursively:

```lean
namespace Mut

mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | succ : Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | succ : Even n → Odd (n + 1)
end

-- Trees with different node types
mutual
  inductive TreeA (α : Type) where
    | leafA : TreeA α
    | nodeA : α → MyList (TreeB α) → TreeA α

  inductive TreeB (α : Type) where
    | leafB : TreeB α
    | nodeB : α → TreeA α → TreeA α → TreeB α
end

end Mut
```
