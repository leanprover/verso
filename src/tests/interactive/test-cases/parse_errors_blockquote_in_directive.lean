import Verso

/-!
This test checks, through the language server, that fixing a parse error in a blockquote inside a
directive clears the error and restores the document's folds and symbols. It matters when you change
a block parser or its error recovery. `VersoTests.IncrementalParsing` checks more documents of this
kind without the language server. `VersoTests.BlockParseErrors` checks where the errors are
reported.

The document has a `:::note` directive whose first block is a blockquote. The edits replace the
blockquote's fourth paragraph, `Thanks`, with `{highlight}[Thanks]` in five steps. While the role is
unfinished, the blockquote and the directive have a parse error. The runner waits for the server
after each edit. After the last edit, it prints the diagnostics, the folding ranges and the document
symbols.

The final text is valid, so the expected output is the same as for a fresh elaboration. It has no
diagnostics. It has folds for the document, the header, the directive and the blockquote. It has the
document symbol `Notes` with its header `Weekend`. A stale error, a missing fold or a missing symbol
would mean that Lean reused a command after text that its parse depends on had changed. Lean reuses
commands correctly when Verso's block commands maintain the incremental parsing invariant, which
`VersoTests.IncrementalParsing` defines.

In prior versions of the blockquote parser, this test failed. On an error, the blockquote failed at
its `>`. Error recovery started there and stopped at the first blank line, before the error. The
output had stale errors (`expected closing ':::'`, `unexpected block opener` and the role error).
The folds for the document, the header, the directive and the blockquote were missing, and so was
the document symbol `Notes`.
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
def highlight : RoleExpanderOf Unit
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

:::note
> The weather was nice today.

  We went for a walk.

  The park was quiet.

  Thanks
  --⬑ delete: "Thanks"
  --⬑ sync
  --⬑ insert: "\x7bhig"
  --⬑ sync
      --⬑ insert: "hli"
  --⬑ sync
         --⬑ insert: "ght"
  --⬑ sync
            --⬑ insert: "\x7d\x5bTh"
  --⬑ sync
                --⬑ insert: "anks\x5d"
  --⬑ collectDiagnostics
  --⬑ textDocument/foldingRange
  --⬑ textDocument/documentSymbol
:::
