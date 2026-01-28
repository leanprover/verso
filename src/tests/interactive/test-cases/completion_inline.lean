import Verso
import VersoManual

open Verso.Genre Manual InlineLean

#doc (Manual) "Test for Completion in Inline Lean" =>

```lean
theorem test : ∀ (n : Nat), n = n := by
  intros
    --^ textDocument/completion
  rfl

def a (x y z : Nat) : x + y + z = x + (y + z):=
  Nat.add_assoc x y z
           --^ textDocument/completion

#print a
```
