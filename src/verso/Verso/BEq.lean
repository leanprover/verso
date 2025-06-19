namespace Verso.BEq

variable {α : Type u}

/--
Compares two values via pointer equality, falling back to the provided predicate.
-/
unsafe def unsafePtrEqThen (beq : α → α → Bool) (x y : α) : Bool :=
  if ptrEq x y then true else beq x y

/--
Compares two values via the provided predicate.

In compiled code, this is overridden by `unsafePtrEqThen`, which attempts pointer equality, falling
back to the provided predicate.
-/
@[implemented_by unsafePtrEqThen]
def ptrEqThen (beq : α → α → Bool) (x y : α) : Bool :=
  beq x y

@[inherit_doc ptrEqThen]
def ptrEqThen' (x y : α) (beq : α → α → Bool) : Bool :=
  ptrEqThen beq x y


/--
Compares two values with their `BEq` instance.

In compiled code, they are first checked for pointer equality.
-/
def ptrBEq [BEq α] (x y : α) : Bool :=
  ptrEqThen (· == ·) x y
