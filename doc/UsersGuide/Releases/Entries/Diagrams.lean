/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 30, 0⟩
  breaking := false
  tag := "feat-diagrams"
  prs := [856]

#doc (Manual) "Diagrams" =>

Add support for {ref "diagrams"}[diagrams]
