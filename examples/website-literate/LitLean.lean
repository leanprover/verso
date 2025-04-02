/-!
# A Literate Lean Post

This post demonstrates the use of Markdown module docstrings to produce a literate Lean page or
post.
-/

/-!

## Preliminaries

Lean code works fine here!
-/
inductive Ty where
  | nat
  | fn : Ty → Ty → Ty

/-!
Here is a bulleted list:
 * `Ty.nat`
 * `Ty.fn`

Here is a numbered list:
1. `Ty.fn Ty.nat Ty.nat`
2. `45`
   * And a bullet
   * And one more

> and a quotation

````
and some code
````
-/
/--
Maps codes for types into actual types
-/
@[reducible] def Ty.denote : Ty → Type
  | nat    => Nat
  | fn a b => a.denote → b.denote


open Ty (nat fn)

/-!

`nat` and `fn` should also highlight.

-/
