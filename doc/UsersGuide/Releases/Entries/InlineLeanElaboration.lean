/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 36, 0⟩
  breaking := false
  tag := "inline-lean-elaboration"
  prs := [1062]

#doc (Manual) "New Helpers for Elaborating Inline Lean Code" =>

In the {name}`Manual` genre, there is a new entry point for metaprograms that elaborate inline Lean code called {name}`elabInlineLean`.
It runs an elaborator action in the scope that the document's Lean code has established, passes the section variables to the action, and arranges for the unused variable linter not to emit spurious warnings for binders in the code.
For code that does not need to re-establish the saved scope, the new helper {name}`withInlineLeanInfoTree` correctly saves info trees.
