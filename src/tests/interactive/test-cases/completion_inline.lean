import Verso
import VersoManual

open Verso.Genre Manual InlineLean

#doc (Manual) "Test for Completion in Inline Lean" =>

```lean
theorem test : ∀ (n : Nat), n = n := by
  intros
     --^ textDocument/completion
  rfl

def a : Nat := Nat.add 3 2
                --^ textDocument/completion

#print a
```
