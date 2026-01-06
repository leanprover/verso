/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Tests.CommentSkipping.Doc

/-!
This test ensures that Lean's parser doesn't skip Lean comment syntax while parsing Verso blocks as
Lean commands.
-/

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
    Verso.Doc.Block.para #[Verso.Doc.Inline.text "def", Verso.Doc.Inline.linebreak "\n"]]
  #[]
-/
#guard_msgs in
#eval %doc Tests.CommentSkipping.Doc
