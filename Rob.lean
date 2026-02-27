import VersoManual
open Verso Doc
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "My Document" =>

This is a Verso document.

It can include inline math, like this: $`x + 4 = -3`.

It can also include block math, like
$$`\int_\mathsf{this}^\mathtt{orthis} \mathit{or{\ldots}maybe{\ldots}this}`

We also support inline lean, like this: {lean}`Nat.add_assoc`.

We also support block lean, like this:

```lean
/-- The name we will be greeting -/
def theName := "Jimothy"

#eval s!"Hello {theName}"
```
