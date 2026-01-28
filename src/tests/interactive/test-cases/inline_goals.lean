import Verso
import VersoManual

theorem test0 : ∀ (n : Nat), n = n := by
  intros
     --^ textDocument/hover
  rfl

open Verso.Genre Manual InlineLean

#doc (Manual) "Test for Goals in Inline Lean" =>

We ship two tests for inline lean codeblocks:

- show hover info over the constant in the codeblock
- shows goals info on a proof

```lean
  --^ textDocument/hover
theorem test : ∀ (n : Nat), n = n := by
  intros
     --^ $/lean/plainGoal
  rfl
```
