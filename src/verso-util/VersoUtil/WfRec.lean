/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/
module

/-!
These two theorems enable automatic termination proofs for functions that recur through `Array.any`.
-/
@[wf_preprocess]
public theorem Array.any_wfParam {xs : Array α} {f : α → Bool} :
    (wfParam xs).any f = xs.attach.unattach.any f := by
  simp [wfParam]

@[wf_preprocess]
public theorem Array.any_unattach {P : α → Prop} {xs : Array (Subtype P)} {f : α → Bool} :
    xs.unattach.any f = xs.any fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]
