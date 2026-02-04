/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso.Method

/-! ## Tests for defmethod macro -/

-- Test fixtures
namespace A.B.C
  structure D where
    field : Nat
  deriving Repr

  structure List (α : Type u) where
    notReallyList : α
end A.B.C

namespace Other

open Verso.Method
open A.B.C

defmethod D.double : D → D
  | ⟨n⟩ => ⟨n*2⟩

/--
error: 'List' is ambiguous - found: A.B.C.List, _root_.List

Please write a more specific namespace.
-/
#guard_msgs in
defmethod List.wat (xs : List Nat) : Nat := 3

end Other

/-- info: { field := 6 } -/
#guard_msgs in
#eval (A.B.C.D.mk 3).double
