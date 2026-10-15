/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mathieu Baudet
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 36, 0⟩
  breaking := false
  tag := "keyboard-page-navigation"
  prs := [1042]

#doc (Manual) "Keyboard Page Navigation" =>

In multi-page HTML output, the left and right arrow keys go to the previous and next page.

The keys follow the links at the bottom of each page, which advertise them with `aria-keyshortcuts`.
They are ignored when a modifier key is held, so that browser shortcuts keep working, and while the focus is in an element that uses the arrow keys itself, such as the search box.
