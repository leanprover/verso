/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 32, 0⟩
  breaking := false
  tag := "method-in-multiverso"
  prs := [903]

#doc (Manual) "Method Moved to MultiVerso" =>

`Verso.Method` is defined in `MultiVerso` and re-exported from its former home, which lets `Verso:shared` build.
