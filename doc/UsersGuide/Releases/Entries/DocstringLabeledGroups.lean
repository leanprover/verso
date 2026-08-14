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
  tag := "docstring-labeled-groups"
  prs := [880]

#doc (Manual) "Labeled Groups in Rendered Docstrings" =>

Labels such as "Fields" and "Constructors" in a rendered declaration are labeled groups.

They were headings, which placed them in the document's heading outline even though they name parts of a declaration rather than sections of the text. Each label is now a paragraph tied by `aria-labelledby` to a container with `role="group"`, so heading navigation reaches the document's own structure.
