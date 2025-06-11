/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

-- ANCHOR: Zipper
class Zipper
    (α : outParam (Type u)) (δ : outParam (Type w))
    (ζ : Type v) where
  move : ζ → δ → Option ζ
  close : ζ → α
  init : α → ζ
-- ANCHOR_END: Zipper

-- ANCHOR: moveNotation
notation:50 z " ⇰ " d => Zipper.move z d
-- ANCHOR_END: moveNotation

-- ANCHOR: LawfulZipper
class LawfulZipper
    (α : Type u) (δ : outParam (Type w)) (ζ : outParam (Type v))
    extends Zipper α δ ζ where
  init_close {x : α} : close (init x) = x
  close_init {x : ζ} : close (init (close x)) = close x
-- ANCHOR_END: LawfulZipper

namespace Zipper

-- ANCHOR: ListZipper
structure ListZipper (α) where
  revBefore : List α
  after : List α
deriving Repr
-- ANCHOR_END: ListZipper

-- ANCHOR: ListZipper.add
def ListZipper.add (x : α) (xs : ListZipper α) : ListZipper α :=
  { xs with after := x :: xs.after }
-- ANCHOR_END: ListZipper.add

-- ANCHOR: ListZipper.close
def ListZipper.close (z : ListZipper α) : List α :=
  close' z.revBefore z.after
where
  close'
    | [], acc => acc
    | x :: xs, acc => close' xs (x :: acc)
-- ANCHOR_END: ListZipper.close

namespace ListZipper

-- ANCHOR: Dir
inductive Dir where
  | left | right
-- ANCHOR_END: Dir

-- ANCHOR: ListZipperInst
instance : Zipper (List α) Dir (ListZipper α) where
  move
    | ⟨[], _⟩, .left => none
    | ⟨x :: pre, post⟩, .left => some ⟨pre, x :: post⟩
    | ⟨_, []⟩, .right => none
    | ⟨pre, x :: post⟩, .right => some ⟨x :: pre, post⟩
  close z := z.close
  init xs := ⟨[], xs⟩
-- ANCHOR_END: ListZipperInst

-- ANCHOR: ListZipperLawful
instance : LawfulZipper (List α) Dir (ListZipper α) where
  init_close := by
    intro xs
    induction xs with
    | nil =>
      simp [init, Zipper.close, ListZipper.close, close.close']
    | cons hd tl ih =>
      simp [init, close, Zipper.close, close.close']
  close_init := by
    intro ⟨revPre, post⟩
    induction revPre <;> simp [init, Zipper.close, close, close.close']
-- ANCHOR_END: ListZipperLawful

-- ANCHOR: ex1
def z1 : ListZipper Nat := Zipper.init [1, 2, 4]
#eval z1 ⇰ .right
-- ANCHOR_END: ex1

-- ANCHOR: ex2
#eval show Option (List Nat) from do
  let z ← z1 ⇰ .right
  let z ← z ⇰ .right
  let z := z.add 3
  pure z.close
-- ANCHOR_END: ex2

end ListZipper


end Zipper
