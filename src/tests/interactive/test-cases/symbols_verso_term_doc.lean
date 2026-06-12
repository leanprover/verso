import Verso
import VersoManual

set_option doc.verso true

open Verso Genre Manual InlineLean
open scoped Verso.Doc.Concrete

-- NOTE: Verso requires headers to be well-nested and to have leading `#`s in column 0.
-- Keep both term bodies flush-left; indented `#`/`##` lines would be parsed as paragraphs.

def termDocsSym := verso (Manual) "Term docs title"
:::::::
# Term docs heading
Term docs text

## Term docs subheading
More term docs text
:::::::

def termDocSym := #doc (Manual) "Term doc title" =>
# Term doc heading
Term text

## Term doc subheading
More term text

* item a
* item b
-- `documentSymbol` is document-scoped in LSP (position ignored by spec).
-- Synchronize first so imports/custom handlers are fully initialized before this request.
--^ sync
--^ textDocument/documentSymbol
