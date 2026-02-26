import Verso
import VersoManual

set_option doc.verso true

open Verso Genre Manual InlineLean

#docs (Manual) docsSym "Docs heading" :=
:::::::
# Docs heading
Text
:::::::
--^ textDocument/documentSymbol

#doc (Manual) "Doc heading" =>
# Doc heading
Text
--^ textDocument/documentSymbol
