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
  breaking := false
  tag := "tex-block-paragraphs"
  prs := [1081]

#doc (Manual) "Paragraph Breaks Between Blocks in TeX Output" =>

While rendering Verso to TeX, the insertion of paragraph breaks between blocks is now controlled by the {name Verso.Doc.TeX.TeXContext.blocksAreParagraphs}`blocksAreParagraphs` field.

Use {name Verso.Doc.TeX.withBlocksNotAsParagraphs}`withBlocksNotAsParagraphs` to disable it and {name Verso.Doc.TeX.withBlocksAsParagraphs}`withBlocksAsParagraphs` to enable paragraph break insertion.
