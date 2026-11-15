/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import VersoTests.CommentSkipping.Doc
import VersoTests.CommentSkipping.Doc2
import VersoTests.DocCommandInput

/-!
These tests check that Lean comments in Verso text are part of their documents, both between blocks
and right after the opening token, which is the `=>` of `#doc` and the opening delimiter of `#docs`
and `verso`. A failure means that a Lean comment in Verso text is missing from the document's
blocks, or that the document isn't defined.
-/

open Lean Verso.Tests.DocCommandInput in
/--
Elaborates `input` as the rest of this module, and logs the elaboration's messages and the blocks of
the document `name`.

The blocks are those of the document's root part, without its sub-parts. When the document isn't
defined, the command logs that instead of the blocks. Without `name`, the document is the one
defined by a `#doc` command.
-/
elab "#document_content " name?:(ident)? input:str : command => do
  let (env, msgs) ← elabModuleRest input.getString
  let name := name?.map (·.getId) |>.getD (Verso.Doc.docName (← getMainModule))
  let msgs := if msgs.isEmpty then msgs else msgs.push '\n'
  if env.contains name then
    let doc ← evalDoc env (← getOptions) name
    logInfo m!"{msgs}{repr doc.toPart.content}"
  else
    logInfo m!"{msgs}The document {name} is not defined."

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Title"]
  "Title"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "/-", Verso.Doc.Inline.linebreak "\n",
        Verso.Doc.Inline.text "This text should be in the document.", Verso.Doc.Inline.linebreak "\n",
        Verso.Doc.Inline.text "-/"],
    Verso.Doc.Block.para #[Verso.Doc.Inline.text "This text is after the Lean comment that should be skipped."],
    Verso.Doc.Block.ul #[{ contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "abc"]] }],
    Verso.Doc.Block.para #[Verso.Doc.Inline.text "/- Also this text should be there -/"],
    Verso.Doc.Block.para #[Verso.Doc.Inline.text "def"]]
  #[]
-/
#test_msgs in
#eval %doc VersoTests.CommentSkipping.Doc

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Title"]
  "Title"
  none
  #[Verso.Doc.Block.blockquote #[],
    Verso.Doc.Block.blockquote
      #[(Verso.Doc.Block.para #[Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "abc")] "http://example.com"])],
    Verso.Doc.Block.blockquote #[(Verso.Doc.Block.para #[Verso.Doc.Inline.text "C"])]]
  #[]
-/
#test_msgs in
#eval %doc VersoTests.CommentSkipping.Doc2

/-! # A Comment Right after the Opening Token -/

/-
This test checks that Lean comments right after the `=>` of `#doc` commands are text in their
documents' first paragraphs. In prior versions of Verso, documents that were only such a comment
were never defined.
-/
/-- info: #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "-- Leaves turn red in the fall."]] -/
#test_msgs in
#document_content "#doc (Verso.Doc.Genre.none) \"Trees\" =>
-- Leaves turn red in the fall.
"

/-
This test checks that Lean comments right after the `=>` of `#doc` terms are text in their
documents' first paragraphs. In prior versions of Verso, the comments were left out of the
documents.
-/
/-- info: #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "-- Leaves turn red in the fall."]] -/
#test_msgs in
#document_content leaves "def leaves : Verso.Doc.VersoDoc Verso.Doc.Genre.none :=
  #doc (Verso.Doc.Genre.none) \"Trees\" =>
-- Leaves turn red in the fall.
"

/-
This test checks that Lean comments right after the opening delimiter of `#docs` commands are text
in their documents' first paragraphs. In prior versions of Verso, the comments were left out of the
documents.
-/
/-- info: #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "-- Leaves turn red in the fall."]] -/
#test_msgs in
#document_content leaves "#docs (Verso.Doc.Genre.none) leaves \"Trees\" :=
:::::::
-- Leaves turn red in the fall.
:::::::
"

/-
This test checks that Lean comments right after the opening delimiter of `verso` terms are text in
their documents' first paragraphs. In prior versions of Verso, the comments were left out of the
documents.
-/
/-- info: #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "-- Leaves turn red in the fall."]] -/
#test_msgs in
#document_content leaves "open Verso.Doc.Concrete in
def leaves : Verso.Doc.VersoDoc Verso.Doc.Genre.none := verso (Verso.Doc.Genre.none) \"Trees\"
:::::::
-- Leaves turn red in the fall.
:::::::
"
