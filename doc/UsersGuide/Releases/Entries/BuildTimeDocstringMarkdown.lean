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
  version := ⟨4, 36, 0⟩
  breaking := true
  tag := "build-time-docstring-markdown"
  prs := [1103]

#doc (Manual) "Offline Docstring Markdown" =>

Markdown in docstrings that are shown in hovers is now rendered to HTML when the site is built.
The `marked` library is no longer used to render them, and it is no longer distributed with Verso.
Some genres loaded the library from a CDN; these genres now work offline.

Breaking changes:
* The constants `Highlighted.WebAssets.marked` and `Highlighted.WebAssets.marked.map` no longer exist, and `verso-literate-html` no longer writes `marked.js`.
* The keys of `Html.katexFonts` now have the form `fonts/...`, relative to the KaTeX stylesheet, rather than `katex/fonts/...`.
* `Verso.Genre.Manual.Markdown.HeaderMapping` is now `Verso.Markdown.HeaderMapping`.
* `Verso.Genre.Blog.Traverse.renderMathJs` no longer exists. The blog's page template loads the bundled KaTeX and `math.js` from `-verso-data/katex/`.
