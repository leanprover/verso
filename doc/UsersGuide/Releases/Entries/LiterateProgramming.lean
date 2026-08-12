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
  tag := "literate429"
  prs := [809]

#doc (Manual) "Literate Programming" =>

Added a zero-config {ref "literate429"}[literate programming] feature.

Verso now supports a simple literate programming system, in which module docstrings are rendered as the text of a page.
While no configuration is necessary to use it, aside from adding Verso as a dependency, some configuration is possible in order to customize aspects of the display.
See {ref "literate"}[its section in this guide] for more details.
