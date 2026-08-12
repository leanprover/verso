/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 28, 0⟩
  breaking := false
  tag := "inline-lean-infoview"
  prs := [700]

#doc (Manual) "Infoview for Inline Lean Code" =>

Fix infoview display for inline lean code, by @david-christiansen and @ejgallego
