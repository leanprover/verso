import Verso
import VersoManual

set_option doc.verso true

open Verso Genre Manual InlineLean

#docs (Manual) docsSymOne "Docs heading one" :=
:::::::
# Docs heading one
Text one

## Docs subheading one
More text one
:::::::
--^ textDocument/documentSymbol

#docs (Manual) docsSymTwo "Docs heading two" :=
:::::::
# Docs heading two
Text two

## Docs subheading two
More text two
:::::::

#docs (Manual) docsSymThree "Docs heading three" :=
:::::::
# Docs heading three
Text three

## Docs subheading three
More text three
:::::::
--^ textDocument/foldingRange
--^ textDocument/documentSymbol
