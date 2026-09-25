/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Hongyu Ouyang
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 35, 0⟩
  breaking := false
  tag := "duplicate-heading-tags"
  prs := [991]

#doc (Manual) "Unique Tags for Repeated Headings" =>

Sections whose titles agree no longer stop the manual from building.

The tag that Verso generates from a section's title takes a numeric suffix when the name it would otherwise use is already taken, but the check that looked for a clash never matched, so repeated titles were given the same tag and traversal reported a duplicate.
Headings in a non-Latin script were affected most, since every unsupported character becomes `___` and titles of the same length therefore produce the same name.
