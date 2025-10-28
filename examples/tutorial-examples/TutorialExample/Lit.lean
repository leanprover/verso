
set_option doc.verso true

/-!
# Literate Verso Tutorial

This tutorial is also not intended as a real learning resource, but instead serves as an example.

Here are two definitions of even-length lists:
-/

inductive EvenList1 (α) where
  | nil
  | cons : α → α → EvenList1 α → EvenList1 α

def EvenList2 (α) := { xs : List α // xs.length % 2 = 0 }

/-!
## Conversions

We can translate both ways, from {name}`EvenList1` to {name}`EvenList2` and vice versa.

One elegant way to do this is to implement the constructors of {name}`EvenList1` as functions on {name}`EvenList2`:
-/

def EvenList2.nil : EvenList2 α := ⟨[], rfl⟩

def EvenList2.cons : α → α → EvenList2 α → EvenList2 α
  | x, y, ⟨xs, prf⟩ => ⟨x :: y :: xs, by grind⟩

def EvenList1.toEvenList2 : EvenList1 α → EvenList2 α
  | .nil => .nil
  | .cons x y xs => .cons x y xs.toEvenList2

/-!
The other direction requires some reasoning.
-/

def EvenList2.toEvenList1 : EvenList2 α → EvenList1 α
  | ⟨[], _⟩ => .nil
  | ⟨x :: y :: xs, _⟩ =>
    let xs : EvenList2 α := ⟨xs, by grind⟩
    .cons x y xs.toEvenList1
termination_by xs => xs.val
