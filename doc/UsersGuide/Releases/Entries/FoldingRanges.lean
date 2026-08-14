/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 29, 0⟩
  breaking := false
  tag := "folding-ranges"
  prs := [768]

#doc (Manual) "Folding Ranges" =>

Fix Verso folding ranges / TOC for Lean.Doc syntax and `#doc`
