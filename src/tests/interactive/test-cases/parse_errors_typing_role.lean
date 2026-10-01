import Verso

/-!
This test checks, through the language server, that the diagnostics and folds after each keystroke
are those of a fresh elaboration of the same text.

The document has a paragraph, a list item, a blockquote and a directive. At the end of the first
line of each block, the edits type a space and the role `{hig}[x]`. The first edit adds the space
and the opening brace, and each later edit adds one character. While the role is unfinished, its
block has a parse error. After each edit, the runner waits for the server and prints the diagnostics
and the folding ranges.

Each state's expected output is the output of a fresh elaboration of the same text. A stale error or
a wrong fold would mean that Lean reused the result of an earlier state of a block that has a parse
error.

In prior versions of the error recovery, this test failed. A block with a parse error became a
command with no syntax of its own. Lean found it equal to the previous state's command and reused
that command's results. From the second broken state of each block on, the output had the error of
the first broken state. In the directive, the folds of the document and its section ended early.
-/

open Lean Verso Doc Elab

/-- A genre with no extensions of its own. -/
def TestGenre : Genre where
  PartMetadata := Unit
  Block := Empty
  Inline := Empty
  TraverseContext := Unit
  TraverseState := Unit

/-- Emphasizes its contents. -/
@[role]
def hig : RoleExpanderOf Unit
  | (), contents => do
    let contents ← contents.mapM elabInline
    ``(Verso.Doc.Inline.emph #[$contents,*])

/-- Groups its blocks. -/
@[directive]
def note : DirectiveExpanderOf Unit
  | (), blocks => do
    let blocks ← blocks.mapM elabBlock
    ``(Verso.Doc.Block.concat #[$blocks,*])

#doc (TestGenre) "Notes" =>

# Weekend

We went for a walk
                  --⬑ insert: " \x7b"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange
                    --⬑ insert: "h"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange
                     --⬑ insert: "i"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange
                      --⬑ insert: "g"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange
                       --⬑ insert: "\x7d"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange
                        --⬑ insert: "\x5b"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange
                         --⬑ insert: "x"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange
                          --⬑ insert: "\x5d"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange

* We saw a heron
                --⬑ insert: " \x7b"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange
                  --⬑ insert: "h"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange
                   --⬑ insert: "i"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange
                    --⬑ insert: "g"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange
                     --⬑ insert: "\x7d"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange
                      --⬑ insert: "\x5b"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange
                       --⬑ insert: "x"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange
                        --⬑ insert: "\x5d"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange

> The park was quiet
                    --⬑ insert: " \x7b"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange
                      --⬑ insert: "h"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange
                       --⬑ insert: "i"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange
                        --⬑ insert: "g"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange
                         --⬑ insert: "\x7d"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange
                          --⬑ insert: "\x5b"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange
                           --⬑ insert: "x"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange
                            --⬑ insert: "\x5d"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange

:::note
The lake was calm
                 --⬑ insert: " \x7b"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange
                   --⬑ insert: "h"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange
                    --⬑ insert: "i"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange
                     --⬑ insert: "g"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange
                      --⬑ insert: "\x7d"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange
                       --⬑ insert: "\x5b"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange
                        --⬑ insert: "x"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange
                         --⬑ insert: "\x5d"
--⬑ collectDiagnostics
--⬑ textDocument/foldingRange
:::

We went home.
