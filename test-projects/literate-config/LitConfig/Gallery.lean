import Lean.Elab.Tactic

/-!
# Code Rendering Gallery

This module exercises every kind of code rendering that Verso produces: messages of
each severity with their hover tooltips, proof states both collapsed and expanded,
output blocks, and documentation hovers. Browser tests and visual inspection use this
page, so it should contain at least one instance of every rendering.

## Warnings

The unfinished definition below carries a {lit}`sorry` warning: its name is underlined,
and hovering it shows the warning tooltip.
-/

/-- Sorts a list, eventually. -/
def gallerySort (xs : List Nat) : List Nat := sorry

/-!
A deprecated constant's use site also warns.
-/

/-- The old name for {name}`gallerySort`. -/
@[deprecated gallerySort (since := "2026-08-10")]
def oldGallerySort (xs : List Nat) : List Nat := gallerySort xs

example : List Nat → List Nat := oldGallerySort

/-!
## Information

Evaluation and elaboration commands produce informational messages, shown both as
hovers on the command and as output blocks.
-/

#eval 2 + 2

#check List.length

/-!
## Errors

The code block below fails to elaborate; the diagnostic is attached to the erroneous
code and shown on hover.

```lean +error
example : Nat := "three"
```
-/

/-!
## Proof States

Tactic proofs carry proof states: hover a tactic to see its state, or click it to
expand the state inline. Case analysis also shows case labels.
-/

theorem galleryAddZero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ k ih => rfl

/-!
A proof that uses {kw (cat := tactic)}`sorry` mixes a warning with proof states.
-/

theorem gallerySorted : 1 + 1 = 2 := by
  have h : 2 = 2 := by rfl
  sorry

open Lean Elab Tactic in
/-- Runs a tactic sequence, first logging a warning that covers the whole proof. -/
elab "flag_proof" ts:tacticSeq : tactic => do
  logWarning "This proof is flagged for review."
  evalTactic ts

/-!
A message can also cover an entire proof, so that the tactics and their proof states are
nested inside the message's span. The {tactic}`flag_proof` tactic warns with the whole
proof as its range.
-/

theorem galleryFlagged (n : Nat) : n + 0 = n := by
  flag_proof
    induction n with
    | zero => rfl
    | succ k ih => rfl

open Lean Elab Tactic in
/-- Runs a tactic sequence, first logging an informational note that covers the whole proof. -/
elab "note_proof" ts:tacticSeq : tactic => do
  logInfo "This proof is worth reading."
  evalTactic ts

/-!
Message regions nest: the whole proof below carries an informational note, and a warning
covers one of its branches.
-/

theorem galleryNoted (n : Nat) : n + 0 = n := by
  note_proof
    induction n with
    | zero => flag_proof rfl
    | succ k ih => rfl

open Lean Elab Tactic in
/-- Runs a tactic sequence, first logging a warning and an informational note that both
cover the whole proof. -/
elab "flag_and_note_proof" ts:tacticSeq : tactic => do
  logWarning "This proof is flagged for review."
  logInfo "This proof is worth reading."
  evalTactic ts

/-!
Messages of different severities can also cover exactly the same range. The region is
styled by the most severe message, and its hover shows both, each with its own severity
styling.
-/

theorem galleryFlaggedAndNoted (n : Nat) : n + 0 = n := by
  flag_and_note_proof rfl

/-!
Messages can also sit inside a proof: the warning below is shown within the tactics, and
its tooltip is also available when the surrounding proof state is expanded.
-/

def galleryOldInProof : List Nat := by
  exact oldGallerySort []

/-!
## Documentation Hovers

Constants with docstrings show them on hover: {name}`gallerySort` has one, and so do
the standard-library names below.
-/

example : Nat := Nat.succ (List.length [1, 2, 3])
