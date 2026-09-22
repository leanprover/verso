/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 35, 0⟩
  breaking := false
  tag := "manual-marginalia"
  prs := [990]

#doc (Manual) "Manual marginalia render in boxes" =>

Marginalia in the manual genre previously had problems when placed in certain boxes, such as tables. Now, they are hoisted up to a level where they can be correctly displayed.
A consequence of this is that, on mobile, marginalia are now shown as popovers instead of toggling text regions.
