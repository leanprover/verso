import Verso

/-!
Document highlight on a list bullet applies to all the bullets of that list and no others.
-/

#docs (.none) docsList "A list in #docs" :=
:::::::
* One
--⬑ sync
--⬑ textDocument/documentHighlight
* Two
:::::::

#doc (.none) "Lists" =>

* One
* Two
--⬑ textDocument/documentHighlight
* Three

1. One
2. Two
--⬑ textDocument/documentHighlight
3. Three

* Outer one

  * Inner one
  --⬑ textDocument/documentHighlight
  * Inner two

* Outer two
--⬑ textDocument/documentHighlight

: First term

  First description

: Second term
--⬑ textDocument/documentHighlight

  Second description
