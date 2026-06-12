import Verso
import VersoManual

set_option doc.verso true

open Verso Genre Manual InlineLean
open scoped Verso.Doc.Concrete

-- NOTE: Verso requires headers to be well-nested and to have leading `#`s in column 0.
-- Keep the term-body content flush-left; indented `#`/`##` lines would be parsed as paragraphs.

def termDocsFold := verso (Manual) "Term docs title"
:::::::
# Term docs heading
Term docs text

## Term docs subheading
More term docs text

* doc item a
* doc item b
:::::::

-- `foldingRange` is document-scoped in LSP; the runner still sends a position from this marker.
-- Synchronize first so imports/custom handlers are fully initialized before this request.
--^ sync
--^ textDocument/foldingRange

def termDocFold := #doc (Manual) "Term doc title" =>
# Term doc heading

Term text

## Term doc subheading

More term text

  * item a
  * item b
