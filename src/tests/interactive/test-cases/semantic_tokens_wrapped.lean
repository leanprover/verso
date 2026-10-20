import Verso
import VersoManual

/-!
Tests semantic highlighting for Verso documents surrounded by colon fences.
-/

open Verso Genre Manual
open scoped Verso.Doc.Concrete

#docs (Manual) wrappedCommand "Command document" :=
:::::::
Command body
:::::::

def wrappedTerm := verso (Manual) "Term document"
:::::::
Term body
:::::::

--^ sync
--^ textDocument/semanticTokens/full
