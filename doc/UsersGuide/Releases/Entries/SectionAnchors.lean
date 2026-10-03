/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 34, 0⟩
  breaking := true
  tag := "manual-heading-anchors"
  prs := [983]

#doc (Manual) "Manual Heading Anchors" =>

Manual title pages and chapters rendered on separate pages now emit their registered section IDs on their headings, so references to these sections resolve correctly.
The fix also applies to the document title in single-page output.

Breaking change: {name}`Verso.Genre.Manual.Html.titlePage` now takes a {name}`Verso.Genre.Manual.Heading` as its first argument instead of plain title HTML.
Callers must supply the heading's level, optional ID, and HTML content.
Manual renderers can use {name}`Verso.Genre.Manual.partHeading` to construct a heading with the registered anchor, section number, and permalink.
