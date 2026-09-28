/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 35, 0⟩
  breaking := false
  tag := "feat-test-widget"
  prs := [959]

#doc (Manual) "Running Tests from the Editor" =>

`Errata` tests can now be run directly from the InfoView using a dedicated widget.
