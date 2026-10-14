/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import Verso

/-!
These tests check where Lean's block parser reports parse errors in Verso documents and ensure
that a `>` begins a blockquote precisely when it's in a block-opening position (and not in the
middle of text).

When a block parser encounters an error after its opening marker, it fails at the error. Error
recovery must resume from this position, without rewinding. This is how Verso's top-level blocks
maintain the Lean command-parsing loop's invariant that each command's syntax, end position, and
parse errors depend on at most two more commands.

Each case runs a block parser on a small input with `ParserFn.test!`. The output lists each error
with its byte offset, its line and column, and the rest of the input from there. Then it shows the
final syntax stack. A recovered error is listed at the position where recovery stopped.
-/

namespace Verso.BlockParseErrorsTest
open Verso.Parser
open Lean.Parser

/-! # Error tests -/

/-
This case checks that a directive fails at an error in its contents. The directive's third paragraph
is the unfinished role `{hig`. The role's error is at the end of its line (6:4), and it is the only
error. The role stops within its paragraph, so the directive's syntax ends with its closing `:::`.
-/
/--
info: Failure @56 (⟨6, 4⟩): unexpected newline; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
Final stack:
  (Lean.Doc.Parser.Block.directive
   (Lean.Doc.Parser.directiveDelimiter ":::")
   `note
   []
   [(Lean.Doc.Parser.Block.para
     [(Lean.Doc.Parser.Inline.text
       (Lean.Doc.Parser.versoText
        "The weather was nice."))])
    (Lean.Doc.Parser.Block.para
     [(Lean.Doc.Parser.Inline.text
       (Lean.Doc.Parser.versoText
        "We went for a walk."))])
    (Lean.Doc.Parser.Block.para
     [(Lean.Doc.Parser.Inline.role
       "{"
       `hig
       []
       <missing>
       []
       []
       [])])]
   (Lean.Doc.Parser.directiveDelimiter ":::"))
Remaining: "\n:::\n"
-/
#test_msgs in
#eval (Lean.Doc.Parser.blockFn {}).test! ":::note\nThe weather was nice.\n\nWe went for a walk.\n\n{hig\n:::\n"

/-
This case checks that a code block fails at an error in its contents. The code block has no closing
fence, so it reads to the end of input and fails there (5:0).
-/
/--
info: Failure @47 (⟨5, 0⟩): unterminated code block opened on line 1; expected '```'
Final stack:
  (Lean.Doc.Parser.Block.codeblock
   (Lean.Doc.Parser.codeBlockFence "```")
   []
   (Lean.Doc.Parser.versoCodeBlock
    [(Lean.Doc.Parser.versoCodeLine
      "The weather was nice.\n")
     (Lean.Doc.Parser.versoCodeLine "\n")
     (Lean.Doc.Parser.versoCodeLine
      "We went for a walk.\n")])
   <missing>)
Remaining: ""
-/
#test_msgs in
#eval (Lean.Doc.Parser.blockFn {}).test! "```\nThe weather was nice.\n\nWe went for a walk.\n"

/-! # Blockquote placement tests -/

/-
A blockquote with two paragraphs, followed by a paragraph, parses with no errors.
-/
/--
info: Success! Final stack:
  [(Lean.Doc.Parser.Block.blockquote
    ">"
    [(Lean.Doc.Parser.Block.para
      [(Lean.Doc.Parser.Inline.text
        (Lean.Doc.Parser.versoText
         "The weather was nice."))])
     (Lean.Doc.Parser.Block.para
      [(Lean.Doc.Parser.Inline.text
        (Lean.Doc.Parser.versoText
         "We went for a walk."))])])
   (Lean.Doc.Parser.Block.para
    [(Lean.Doc.Parser.Inline.text
      (Lean.Doc.Parser.versoText "We came home."))
     (Lean.Doc.Parser.Inline.linebreak "\n")])]
All input consumed.
-/
#test_msgs in
#eval (document).test! "> The weather was nice.\n\n  We went for a walk.\n\nWe came home.\n"

/-
A `>` alone on its line is an empty blockquote.
-/
/--
info: Success! Final stack:
  [(Lean.Doc.Parser.Block.blockquote ">" [])
   (Lean.Doc.Parser.Block.para
    [(Lean.Doc.Parser.Inline.text
      (Lean.Doc.Parser.versoText "We came home."))
     (Lean.Doc.Parser.Inline.linebreak "\n")])]
All input consumed.
-/
#test_msgs in
#eval (document).test! ">\n\nWe came home.\n"

/-
A `>` in the middle of a line is text, not a blockquote.
-/
/--
info: Success! Final stack:
  [(Lean.Doc.Parser.Block.para
    [(Lean.Doc.Parser.Inline.text
      (Lean.Doc.Parser.versoText "Also, 2 > 3."))
     (Lean.Doc.Parser.Inline.linebreak "\n")])]
All input consumed.
-/
#test_msgs in
#eval (document).test! "Also, 2 > 3.\n"

/-
A `>` that is indented less than a list item's contents ends the list and begins a blockquote. The
`>` is at column 0, and the item's contents are at column 2.
-/
/--
info: Success! Final stack:
  [(Lean.Doc.Parser.Block.ul
    [(Lean.Doc.Parser.ListItem.item
      (Lean.Doc.Parser.listMarker "*")
      [(Lean.Doc.Parser.Block.para
        [(Lean.Doc.Parser.Inline.text
          (Lean.Doc.Parser.versoText
           "The weather was nice."))])])])
   (Lean.Doc.Parser.Block.blockquote
    ">"
    [(Lean.Doc.Parser.Block.para
      [(Lean.Doc.Parser.Inline.text
        (Lean.Doc.Parser.versoText
         "We went for a walk."))
       (Lean.Doc.Parser.Inline.linebreak
        "\n")])])]
All input consumed.
-/
#test_msgs in
#eval (document).test! "* The weather was nice.\n\n> We went for a walk.\n"

/-
A `>` that is indented less than the required column is not a blockquote. Here the saved position is
at column 2, so blocks must start at column 2 or later. The `>` is at column 0. The parser fails at 1:0 and consumes no input, because the
error comes before the opening marker. This lets an enclosing block end at that line.
-/
/--
info: Failure @0 (⟨1, 0⟩): expected block with indentation at least 2
Final stack:
  <missing>
Remaining: "> The weather was nice.\n"
-/
#test_msgs in
#eval (adaptCacheableContextFn ({ · with savedPos? := some ⟨2⟩ }) (Lean.Doc.Parser.blockFn {})).test! "> The weather was nice.\n"
