/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import Verso
import VersoTests.DocCommandInput

/-!
These tests check that a block's syntax and content don't depend on whether it is the document's
last block, and that a `#doc` and `#docs` elaborate the same document from the same text.
-/

namespace Verso.FinalLineBreakTest

open Lean Elab Command
open Verso Doc
open Verso.Tests.DocCommandInput

/-- The text of a `#doc` command before its document. -/
def docCommandStart : String := "#doc (Verso.Doc.Genre.none) \"Trees\" =>\n\n"

/-- The syntax of the top-level blocks of a `#doc` command whose document is `text`. -/
def topLevelBlocks (text : String) : CommandElabM (Array Syntax) := do
  let inputCtx := Parser.mkInputContext (docCommandStart ++ text) "<doc>"
  let commandState : Command.State := { env := (← getEnv), maxRecDepth := (← get).maxRecDepth }
  let s ← IO.processCommands inputCtx {} commandState
  return s.commands.filterMap fun cmd =>
    if cmd.isOfKind ``Verso.Doc.Concrete.addBlockCmd ||
        cmd.isOfKind ``Verso.Doc.Concrete.addLastBlockCmd then
      some cmd[0]
    else none

/--
Logs whether the last block of a `#doc` command whose document is `text` has the same syntax as the
same block followed by a blank line and a paragraph, apart from the trailing whitespace of its last
token. When the two differ, it logs both. The text ends with a line break.
-/
elab "#last_block_syntax " text:str : command => do
  let last ← topLevelBlocks text.getString
  let followed ← topLevelBlocks (text.getString ++ "\nMycelium spreads.\n")
  let some block := last.back? | throwError "The document has no blocks."
  let some block' := followed[last.size - 1]?
    | throwError "The followed document has too few blocks."
  let block := block.unsetTrailing
  let block' := block'.unsetTrailing
  if block.eqWithInfo block' then
    logInfo "same syntax"
  else
    logInfo m!"different syntax\nlast:{indentD (block.formatStx (showInfo := true))}\n\
      followed:{indentD (block'.formatStx (showInfo := true))}"

/--
Elaborates `input` and returns the document named `name` that it defines, shown with `repr`, after
the messages of the elaboration.
-/
def docOf (input : String) (name : Name) : CommandElabM String := do
  let (env, msgs) ← elabModuleRest input
  match ← (evalDoc env (← getOptions) name).toBaseIO with
  | .ok doc => return s!"{msgs}\n{repr doc.toPart}"
  | .error e => return s!"{msgs}\nevaluation failed: {e}"

/-- The document of a `#doc` command whose document is `text`. -/
def docCommandDoc (text : String) : CommandElabM String := do
  docOf (docCommandStart ++ text) (docName (← getMainModule))

/-- The document of a `#doc` term whose document is `text`. -/
def docTermDoc (text : String) : CommandElabM String :=
  docOf ("def termDoc : Verso.Doc.VersoDoc Verso.Doc.Genre.none := " ++ docCommandStart ++ text)
    `termDoc

/-- The document of a `#docs` command whose document is `text`, which ends with a line break. -/
def docsDoc (text : String) : CommandElabM String :=
  docOf ("#docs (Verso.Doc.Genre.none) docsDoc \"Trees\" :=\n:::::::\n" ++ text ++ ":::::::\n")
    `docsDoc

/--
Logs whether a `#doc` command and a `#docs` command whose document is `text` define the same
document. When they differ, it logs both.
-/
elab "#doc_command_and_docs " text:str : command => do
  let doc ← docCommandDoc text.getString
  let docs ← docsDoc text.getString
  if doc == docs then logInfo "same document"
  else logInfo m!"different documents\n#doc:\n{doc}\n#docs:\n{docs}"

/--
Logs whether a `#doc` term and a `#docs` command whose document is `text` define the same document.
When they differ, it logs both.
-/
elab "#doc_term_and_docs " text:str : command => do
  let doc ← docTermDoc text.getString
  let docs ← docsDoc text.getString
  if doc == docs then logInfo "same document"
  else logInfo m!"different documents\n#doc:\n{doc}\n#docs:\n{docs}"

/--
Logs whether `#doc` commands whose documents are `text` followed by no line break, by one and by
three define the same document.
-/
elab "#final_line_breaks " text:str : command => do
  let none ← docCommandDoc text.getString
  let one ← docCommandDoc (text.getString ++ "\n")
  let three ← docCommandDoc (text.getString ++ "\n\n\n")
  if none == one && one == three then logInfo "same document"
  else logInfo m!"different documents\nno line break:\n{none}\none:\n{one}\nthree:\n{three}"

/-! # The Last Block's Syntax -/

/-
This test checks that a paragraph has the same syntax when it is the last block as when another
block follows it. The line break that ends the paragraph is trailing whitespace in both.
-/
/-- info: same syntax -/
#test_msgs in
#last_block_syntax "Trees grow.

Leaves turn red.
"

/-
This test checks that a list whose last item ends in a paragraph has the same syntax when it is the
last block as when another block follows it.
-/
/-- info: same syntax -/
#test_msgs in
#last_block_syntax "Trees grow.

* Oak
* Maple
"

/-
This test checks that a blockquote has the same syntax when it is the last block as when another
block follows it.
-/
/-- info: same syntax -/
#test_msgs in
#last_block_syntax "Trees grow.

> Leaves turn red.
"

/-
This test checks that a description list has the same syntax when it is the last block as when
another block follows it.
-/
/-- info: same syntax -/
#test_msgs in
#last_block_syntax "Trees grow.

: Mycelium

  The threads of a fungus.
"

/-
This test checks that a footnote definition has the same syntax when it is the last block as when
another block follows it.
-/
/-- info: same syntax -/
#test_msgs in
#last_block_syntax "Trees grow.[^fungi]

[^fungi]: Mycelium links their roots.
"

/-
This test checks that a paragraph with a parse error, an unclosed `*`, has the same syntax when it
is the last block as when another block follows it. Its final line break is inside an inline, the
unclosed bold text, rather than directly in the paragraph.
-/
/-- info: same syntax -/
#test_msgs in
#last_block_syntax "Trees grow.

Leaves *turn red.
"

/-
This test checks that a line break that ends a role's contents stays in the last block, so the block
has the same syntax as when another block follows it. The line break is right before the role's
closing bracket.
-/
/-- info: same syntax -/
#test_msgs in
#last_block_syntax "Trees grow.

Leaves {index}[turn red
]
"

/-
This test checks that a line break that ends a link's text stays in the last block, so the block
has the same syntax as when another block follows it. The line break is right before the link text's
closing bracket.
-/
/-- info: same syntax -/
#test_msgs in
#last_block_syntax "Trees grow.

Leaves [turn red
](https://example.com)
"

/-! # The Forms of a Document -/

/-
This test checks that a `#doc` command and a `#docs` command define the same document when the text
ends with a paragraph.
-/
/-- info: same document -/
#test_msgs in
#doc_command_and_docs "Trees grow.

Leaves turn red.
"

/-
This test checks that a `#doc` command and a `#docs` command define the same document when the text
ends with a footnote definition. The footnote's contents appear in the paragraph that uses it.
-/
/-- info: same document -/
#test_msgs in
#doc_command_and_docs "Trees grow.[^fungi]

[^fungi]: Mycelium links their roots.
"

/-
This test checks that a `#doc` term and a `#docs` command define the same document when the text
ends with a paragraph.
-/
/-- info: same document -/
#test_msgs in
#doc_term_and_docs "Trees grow.

Leaves turn red.
"

/-
This test checks that a `#doc` term and a `#docs` command define the same document when the text
ends with a footnote definition.
-/
/-- info: same document -/
#test_msgs in
#doc_term_and_docs "Trees grow.[^fungi]

[^fungi]: Mycelium links their roots.
"

/-! # Line Breaks at the End of the File -/

/-
This test checks that a document that ends in a paragraph is the same whether the file ends right
after the paragraph's text, after one line break or after several.
-/
/-- info: same document -/
#test_msgs in
#final_line_breaks "Trees grow.

Leaves turn red."
