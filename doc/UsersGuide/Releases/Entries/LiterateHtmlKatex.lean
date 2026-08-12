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
  tag := "literate-html-katex"
  prs := [899]

#doc (Manual) "Math in Literate HTML" =>

Math written in module docstrings is rendered with KaTeX in the HTML that `verso-literate-html` produces.
