/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

set_option doc.verso true

namespace Verso.BEq

variable {α : Type u}

/--
Compares two values via pointer equality, falling back to the provided predicate.
-/
public unsafe def unsafePtrEqThen (beq : α → α → Bool) (x y : α) : Bool :=
  if ptrEq x y then true else beq x y

/--
Compares two values via the provided predicate.

In compiled code, this is overridden by {name}`unsafePtrEqThen`, which attempts pointer equality, falling
back to the provided predicate.
-/
@[implemented_by unsafePtrEqThen]
public def ptrEqThen (beq : α → α → Bool) (x y : α) : Bool :=
  beq x y

@[inherit_doc ptrEqThen]
public def ptrEqThen' (x y : α) (beq : α → α → Bool) : Bool :=
  ptrEqThen beq x y


/--
Compares two values with their {name}`BEq` instance.

In compiled code, they are first checked for pointer equality.
-/
public def ptrBEq [BEq α] (x y : α) : Bool :=
  ptrEqThen (· == ·) x y
