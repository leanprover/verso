/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import DemoTextbook.Meta.Lean
import DemoTextbook.Papers

-- This is a chapter that's included
import DemoTextbook.Nat

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean


open DemoTextbook

set_option pp.rawOnError true



#doc (Manual) "A Textbook" =>

%%%
authors := ["David Thrane Christiansen"]
%%%

{index}[example]
Here's an example project showing how to build a certain kind of textbook with Verso.
It's a good idea to read the document's source together with the rendered output, because it demonstrates how to use various features.


# Lean Code

The tools in this section come from the Verso namespace `Verso.Genre.Manual.InlineLean`.

The {lean}`lean` code block allows Lean code to be included in the text.
It is elaborated in the context of the text's elaboration, but in a separate section scope (so the set of variables and opened namespaces can be controlled).

```lean
inductive NatList where
  | nil
  | cons : Nat → NatList → NatList
```

Use the {lean}`leanSection` directive to create a Lean section that delimits scope changes.
The {lean}`lean` role allows Lean terms to be included as inline elements in paragraphs.
Use {lean}`name` to refer to a name that can't be easily elaborated as a term, e.g. due to implicit parameters.

## Saved Lean Code

The tools in this section come from the Verso namespace `DemoTextbook` in the module `DemoTextbook.Meta.Lean`.

The {lean}`savedLean` code block is just like the {lean}`lean` block, except it additionally saves the contents to a file when the book is built.
The code is saved to the output directory, in the subdirectory `example-code` (by default, this is `_out/example-code`), with its filename being that of the file in which it is edited.
Use {lean}`savedImport` to save code for the file header.

```savedComment
Here's some commentary for the file
```
```savedLean
def x : Nat := 15
```

When named, the code block's output is saved.
It can be both checked and included in the document using {lean}`leanOutput`:

```savedLean (name := xVal)
#eval x
```
```leanOutput xVal
15
```

Expected error messages must be indicated explicitly:
```lean (error := true) (name := yVal)
#eval y
```
```leanOutput yVal
Unknown identifier `y`
```

{include 1 DemoTextbook.Nat}

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
