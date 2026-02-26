import Verso
import VersoManual

set_option doc.verso true

open Verso Genre Manual InlineLean

/--
# Docstring heading
Text

* one
* two
-/
def ds : Nat :=
0

#docs (Manual) docsFoldOne "Docs title" :=
:::::::
# Docs heading one
Text one

## Docs subheading one
More text one

* one
* two

```lean
#check Nat.succ
```
:::::::

#docs (Manual) docsFoldTwo "Docs title" :=
:::::::
# Docs heading two
Text two

## Docs subheading two
More text two

* three
* four
:::::::

-- `foldingRange` is document-scoped in LSP; the runner still sends a position from this marker.
-- Synchronize first so imports/custom handlers are fully initialized before this request.
--^ sync
--^ textDocument/foldingRange

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
