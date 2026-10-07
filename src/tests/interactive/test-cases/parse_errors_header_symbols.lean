import Verso

/-!
This test checks, through the language server, that a header with a parse error still has its
document symbol, so the outline stays stable while the header is typed. It also checks that the
diagnostics and symbols after each keystroke are those of a fresh elaboration of the same text. It matters when you change error recovery or how headers make parts.
The editor's outline shows these symbols while a header is being typed.

The document has two sections, `Weekend` and `Monday`. At the end of the `Weekend` header, the edits
type a space and the role `{hig}[x]`. The first edit adds the space and the opening brace, and each
later edit adds one character. While the role is unfinished, the header has a parse error. After each
edit, the runner waits for the server and prints the diagnostics and the document symbols.

In every state except `# Weekend {hig}`, the symbols are `TestGenre`, `hig`, the document `Notes`
and its sections `Weekend ` and `Monday`, and `Weekend ` covers the lines up to `Monday`. While
`{hig` is typed, the title is the text that the header's parser read before the error, `Weekend `
with its trailing space. From the opening bracket on, it is `Weekend ` and the role's contents, as
in `Weekend  x`. In `# Weekend {hig}`, the header fails after `}`, has no effect and has no symbol.

In prior versions of the error recovery, a header with a parse error was a `sorry` block in the
document, and the outline had no section `Weekend` while the role was unfinished.
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

#doc (TestGenre) "Notes" =>

# Weekend
         --⬑ insert: " \x7b"
--⬑ collectDiagnostics
--⬑ textDocument/documentSymbol
           --⬑ insert: "h"
--⬑ collectDiagnostics
--⬑ textDocument/documentSymbol
            --⬑ insert: "i"
--⬑ collectDiagnostics
--⬑ textDocument/documentSymbol
             --⬑ insert: "g"
--⬑ collectDiagnostics
--⬑ textDocument/documentSymbol
              --⬑ insert: "\x7d"
--⬑ collectDiagnostics
--⬑ textDocument/documentSymbol
               --⬑ insert: "\x5b"
--⬑ collectDiagnostics
--⬑ textDocument/documentSymbol
                --⬑ insert: "x"
--⬑ collectDiagnostics
--⬑ textDocument/documentSymbol
                 --⬑ insert: "\x5d"
--⬑ collectDiagnostics
--⬑ textDocument/documentSymbol

We went for a walk.

# Monday

We went to work.
