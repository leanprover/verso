/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import PackageManual.Papers
import PackageManual.DocFeatures

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean


open PackageManual

set_option pp.rawOnError true

-- This is the source of code examples to be shown in the document. It should be relative to the
-- current Lake workspace. One good way to set up the files is in a Git repository that contains one
-- Lake package for example code and another for the docs, as sibling directories.
set_option verso.exampleProject "examples/documented-package"

-- This is the module that will be consulted for example code. It can be overridden using the
-- `(module := ...)` argument to most elements that show code.
set_option verso.exampleModule "Zippers"

open Verso.Code.External

#doc (Manual) "Zippers: A Documentation Example" =>
%%%
authors := ["David Thrane Christiansen"]
shortTitle := "Zippers"
%%%

{index}[example]
Here's an example project showing how to document a Lean package with Verso.
It's a good idea to read the document's source together with the rendered output, because it demonstrates how to use various features.

This document's setup has the following properties:
 * It decouples the version of Lean used for Verso from that used by the library. This is important because it allows a library to stay on an older version of Lean while still adopting improvements to Verso that require new compiler versions.
 * The example code may use any Lean syntax, including custom syntax, and it will be highlighted correctly.
 * Examples to be included in the documentation are indicated with special comments.

The library here was chosen to be small.
It is not intended as a realistic library, but rather to exercise certain interesting features.

# Zippers

A _zipper_{citep theZipper}[] is a purely-functional cursor into a data structure.
They're equivalent to maintaining a description of a position (e.g. an index into a list or a series of left-right subtree decisions in a tree), but do not require traversing the prefix of the data structure.
Zippers are efficient when many modifications to a persistent structure are concentrated near each other.

:::paragraph
In this example zipper library, a zipper for some type {anchorTerm Zipper}`α` is indicated with an instance of {anchorTerm Zipper}`Zipper`:

```anchor Zipper
class Zipper
    (α : outParam (Type u)) (δ : outParam (Type w))
    (ζ : Type v) where
  move : ζ → δ → Option ζ
  close : ζ → α
  init : α → ζ
```

The type {anchorTerm Zipper}`δ` indicates the directions in which a zipper may move.
:::

:::paragraph
A lawful zipper is one in which initializing and closing zippers are inverse.
A lawful zipper for some type {anchorTerm LawfulZipper}`α` is indicated with an instance of {anchorTerm LawfulZipper}`LawfulZipper`:

```anchor LawfulZipper
class LawfulZipper
    (α : Type u) (δ : outParam (Type w)) (ζ : outParam (Type v))
    extends Zipper α δ ζ where
  init_close {x : α} : close (init x) = x
  close_init {x : ζ} : close (init (close x)) = close x
```
:::

:::paragraph
There's some syntax for moving a zipper.
The `⇰` operator attempts to move in a direction.
Here's a list zipper in action:
```anchor ex1
def z1 : ListZipper Nat := Zipper.init [1, 2, 4]
#eval z1 ⇰ .right
```
```anchorInfo ex1
some { revBefore := [1], after := [2, 4] }
```

```anchor ex2
#eval show Option (List Nat) from do
  let z ← z1 ⇰ .right
  let z ← z ⇰ .right
  let z := z.add 3
  pure z.close
```
```anchorInfo ex2
some [1, 2, 3, 4]
```
:::

:::paragraph
List zippers are defined as follows:
```anchor ListZipper
structure ListZipper (α) where
  revBefore : List α
  after : List α
deriving Repr
```
They contain the reversed prefix to the current point and the suffix after it.
To convert them back to a list, use {anchorName ListZipper.close (show:=close)}`ListZipper.close`:
```anchor ListZipper.close
def ListZipper.close (z : ListZipper α) : List α :=
  close' z.revBefore z.after
where
  close'
    | [], acc => acc
    | x :: xs, acc => close' xs (x :: acc)
```
To add an element at the current position, use {anchorName ListZipper.add (show:=add)}`ListZipper.add`:
```anchor ListZipper.add
def ListZipper.add (x : α) (xs : ListZipper α) : ListZipper α :=
  { xs with after := x :: xs.after }
```
:::

:::paragraph
Here's the instance:
```anchor Dir
inductive Dir where
  | left | right
```
```anchor ListZipperInst
instance : Zipper (List α) Dir (ListZipper α) where
  move
    | ⟨[], _⟩, .left => none
    | ⟨x :: pre, post⟩, .left => some ⟨pre, x :: post⟩
    | ⟨_, []⟩, .right => none
    | ⟨pre, x :: post⟩, .right => some ⟨x :: pre, post⟩
  close z := z.close
  init xs := ⟨[], xs⟩
```

:::

{include 1 PackageManual.DocFeatures}

# Notes

Use {lean}`margin` to create a marginal note.{margin}[Marginal notes should be used like footnotes.]

# Citations

Cite works using {lean}`citet`, {lean}`citep`, or {lean}`citehere`.
They take a name of a citable reference value as a parameter.
References should be defined as values, typically in one module that is imported (similar to the role of a `.bib` file in LaTeX).

Textual citations, as with {citet someThesis}[], look like this.
Parenthetical {citep someArXiv}[] looks like this.
Use {lean}`citehere` to literally include the cite rather than making a margin note, e.g. {citehere somePaper}[].
Literally-included cites are mostly useful when performing citation inside a margin note.

# Section References
%%%
tag := "sec-ref"
%%%

Sections with tags can be cross-referenced.
They additionally gain permalink indicators that can be used to link to them even if the document is reorganized.
Tags are added in section metadata, e.g.
```
%%%
tag := "my-tag"
%%%
```
They can be linked to using {lean}`ref`.
Here's one to {ref "sec-ref"}[this section].



# Viewing the Output

Verso's HTML doesn't presently work correctly when opened directly in a browser, so it should be served via a server.{margin}[This is due to security restrictions on retrieved files: some of the code hovers are deduplicated to a JSON file that's fetched on demand.]
Python has a simple web server module that's useful for this.
In the output directory, run:
```
python3 -m http.server 8000 --directory .
```
The port and root can be customized by modifying the appropriate parameters.

One downside of this simple server is that it sets cache headers optimistically.
If incorrect hovers are appearing locally, then try disabling caching in your browser's development tools.

# Using an Index

{index}[index]
The index should contain an entry for “lorem ipsum”.
{index}[lorem ipsum] foo
{index subterm:="of lorem"}[ipsum]
{index subterm:="per se"}[ipsum]
{index}[ipsum]
Lorem ipsum dolor {index}[dolor] sit amet, consectetur adipiscing elit, sed {index}[sed] do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris {index}[laboris] {see "lorem ipsum"}[laboris] {seeAlso "dolor"}[laboris] nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

This is done using the `{index}[term]` syntax. Sub-terms {index subterm:="sub-term"}[entry] can be added using the `subterm` parameter to `index`.

Multiple index {index}[index] targets for a term also work.

{ref "index"}[Index link]


# Index
%%%
number := false
tag := "index"
%%%

{theIndex}
