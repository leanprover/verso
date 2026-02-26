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

#docs (Manual) docsSymTwo "Docs title two" :=
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

#doc (Manual) "Doc heading" =>
# Doc heading
Text and text

## Doc subheading
More text

* one
* two

```lean
#check Nat.succ
```

```lean (name := symbolOut)
#eval 1 + 1
```

```leanOutput symbolOut
2
```
-- `documentSymbol` is document-scoped in LSP (position ignored by spec).
-- Synchronize first so imports/custom handlers are fully initialized before this request.
--^ sync
--^ textDocument/documentSymbol
