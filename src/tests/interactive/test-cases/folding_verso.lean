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
--^ textDocument/foldingRange

#docs (Manual) docsFoldOne "Docs heading one" :=
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
--^ textDocument/foldingRange

#docs (Manual) docsFoldTwo "Docs heading two" :=
:::::::
# Docs heading two
Text two

## Docs subheading two
More text two

* three
* four
:::::::
--^ textDocument/foldingRange

#doc (Manual) "Doc heading" =>
# Doc heading
Text and text

## Doc subheading
More text

* one
* two
--^ textDocument/foldingRange

```lean
#check Nat.succ
```
