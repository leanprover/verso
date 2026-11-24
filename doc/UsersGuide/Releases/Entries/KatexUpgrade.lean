/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

set_option linter.verso.manual.headerTags false

release_note
  version := ⟨4, 37, 0⟩
  breaking := false
  tag := "katex-upgrade"
  prs := [1127]

#doc (Manual) "KaTeX 0.19" =>

The bundled KaTeX is now version 0.19.1.

In this version, the class of the element that is placed around rendered math is now `katex-base` rather than `base`.
Custom stylesheets that select `.katex .base` should instead select `.katex .katex-base`.
