import Verso
import VersoManual

set_option doc.verso true

/-- This shows $`\forall n, n = n`
               --^ $/lean/plainTermGoal
-/
theorem test0 : ∀ (n : Nat), n = n := by
  intros
  rfl

open Verso.Genre

-- Can we avoid using the Manual Genre here?
#doc (Manual) "Test for verso math elaboration" =>

This is a standard paragraph, see some *inline* text decorations.
                                      --^ $/lean/plainTermGoal

Our previous theorem showed $`\forall n, n = n`, which is equivalent to
                            --^ $/lean/plainTermGoal

$$`
\forall n, n = n
      --^ $/lean/plainTermGoal
`
