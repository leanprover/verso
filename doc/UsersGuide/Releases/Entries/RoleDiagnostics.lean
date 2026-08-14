/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 31, 0⟩
  breaking := false
  tag := "role-diagnostics"
  prs := [763]

#doc (Manual) "Role Resolution Diagnostics" =>

Improve role resolution diagnostics with suggestions and actionable registration errors.
