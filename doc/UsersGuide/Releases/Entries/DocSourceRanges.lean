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
  tag := "doc-source-ranges"
  prs := [771]

#doc (Manual) "Source Ranges for Documents" =>

Preserve `#doc`/`#docs` source ranges for LSP document symbols and folding ranges.
