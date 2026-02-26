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

#docs (Manual) docsFold "Docs heading" :=
:::::::
# Docs heading
Text

* one
* two

```lean
#check Nat.succ
```
:::::::
--^ textDocument/foldingRange

#doc (Manual) "Doc heading" =>
# Doc heading
Text and text

* one
* two

```lean
#check Nat.succ
```
--^ textDocument/foldingRange
