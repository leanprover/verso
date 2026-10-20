/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio J. Gallego Arias
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 36, 0⟩
  breaking := true
  tag := "manual-heading-ids"
  prs := [983]

#doc (Manual) "Section IDs on Manual Headings" =>

Manual title pages and chapters rendered on separate pages now carry their registered section IDs as the `id` attribute of their headings, so links to these sections resolve correctly.
The document title in single-page output also carries its ID.

Breaking change: {name}`Verso.Genre.Manual.Html.titlePage` now takes a {name}`Verso.Genre.Manual.Heading` as its first argument instead of plain title HTML.
Callers must supply the heading's level, optional ID, and HTML content.
Manual renderers can use {name}`Verso.Genre.Manual.partHeading` to construct a heading with the registered `id` attribute, section number, and permalink.
