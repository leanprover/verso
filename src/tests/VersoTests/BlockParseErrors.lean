/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import Verso

/-!
These tests check where Verso's block parsers report parse errors and ensure that a `>` begins a
blockquote precisely when it's in a block-opening position (and not in the middle of text).

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
is the unfinished role `{hig`. The role's error is at the end of its line (6:4). The directive fails
at the end of input (8:0), because the unclosed role reads past the closing `:::`.
-/
/--
info: 2 failures:
  @56 (⟨6, 4⟩): unexpected '
'; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
    "\n:::\n"
  @61 (⟨8, 0⟩): unexpected end of input; expected '![', '$$', '$', '*', '[', '[^', '_', '`' or '{'
    ""

Final stack:
  (Lean.Doc.Syntax.directive
   ":::"
   `note
   []
   "\n"
   [(Lean.Doc.Syntax.para
     "para{"
     [(Lean.Doc.Syntax.text
       (str "\"The weather was nice.\""))]
     "}")
    (Lean.Doc.Syntax.para
     "para{"
     [(Lean.Doc.Syntax.text
       (str "\"We went for a walk.\""))]
     "}")
    (Lean.Doc.Syntax.para
     "para{"
     [(Lean.Doc.Syntax.role
       "{"
       `hig
       []
       <missing>
       "["
       [(Lean.Doc.Syntax.footnote <missing>)]
       "]")])])
-/
#test_msgs in
#eval (block {}).test! ":::note\nThe weather was nice.\n\nWe went for a walk.\n\n{hig\n:::\n"

/-
This case checks that a code block fails at an error in its contents. The code block has no closing
fence, so it reads to the end of input and fails there (5:0).
-/
/--
info: Failure @47 (⟨5, 0⟩): unexpected end of input
Final stack:
  (Lean.Doc.Syntax.codeblock
   "```"
   []
   "\n"
   (str
    "\"The weather was nice.\\n\\nWe went for a walk.\\n\"")
   <missing>)
Remaining: ""
-/
#test_msgs in
#eval (block {}).test! "```\nThe weather was nice.\n\nWe went for a walk.\n"

/-! # Blockquote placement tests -/

/-
A blockquote with two paragraphs, followed by a paragraph, parses with no errors.
-/
/--
info: Success! Final stack:
  [(Lean.Doc.Syntax.blockquote
    ">"
    [(Lean.Doc.Syntax.para
      "para{"
      [(Lean.Doc.Syntax.text
        (str "\"The weather was nice.\""))]
      "}")
     (Lean.Doc.Syntax.para
      "para{"
      [(Lean.Doc.Syntax.text
        (str "\"We went for a walk.\""))]
      "}")])
   (Lean.Doc.Syntax.para
    "para{"
    [(Lean.Doc.Syntax.text
      (str "\"We came home.\""))
     (Lean.Doc.Syntax.linebreak
      "line!"
      (str "\"\\n\""))]
    "}")]
All input consumed.
-/
#test_msgs in
#eval (document).test! "> The weather was nice.\n\n  We went for a walk.\n\nWe came home.\n"

/-
A `>` alone on its line is an empty blockquote.
-/
/--
info: Success! Final stack:
  [(Lean.Doc.Syntax.blockquote ">" [])
   (Lean.Doc.Syntax.para
    "para{"
    [(Lean.Doc.Syntax.text
      (str "\"We came home.\""))
     (Lean.Doc.Syntax.linebreak
      "line!"
      (str "\"\\n\""))]
    "}")]
All input consumed.
-/
#test_msgs in
#eval (document).test! ">\n\nWe came home.\n"

/-
A `>` in the middle of a line is text, not a blockquote.
-/
/--
info: Success! Final stack:
  [(Lean.Doc.Syntax.para
    "para{"
    [(Lean.Doc.Syntax.text
      (str "\"Also, 2 > 3.\""))
     (Lean.Doc.Syntax.linebreak
      "line!"
      (str "\"\\n\""))]
    "}")]
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
  [(Lean.Doc.Syntax.ul
    "ul{"
    [(Lean.Doc.Syntax.li
      "*"
      [(Lean.Doc.Syntax.para
        "para{"
        [(Lean.Doc.Syntax.text
          (str "\"The weather was nice.\""))]
        "}")])]
    "}")
   (Lean.Doc.Syntax.blockquote
    ">"
    [(Lean.Doc.Syntax.para
      "para{"
      [(Lean.Doc.Syntax.text
        (str "\"We went for a walk.\""))
       (Lean.Doc.Syntax.linebreak
        "line!"
        (str "\"\\n\""))]
      "}")])]
All input consumed.
-/
#test_msgs in
#eval (document).test! "* The weather was nice.\n\n> We went for a walk.\n"

/-
A `>` that is indented less than the required column is not a blockquote. Here blocks must start at
column 2, and the `>` is at column 0. The parser fails at 1:0 and consumes no input, because the
error comes before the opening marker. This lets an enclosing block end at that line.
-/
/--
info: Failure @0 (⟨1, 0⟩): unexpected block opener; expected %%% (at line beginning) or expected column at least 2
Final stack:
  (Lean.Doc.Syntax.metadata_block
   <missing>
   <missing>)
Remaining: "> The weather was nice.\n"
-/
#test_msgs in
#eval (block { minIndent := 2 }).test! "> The weather was nice.\n"
