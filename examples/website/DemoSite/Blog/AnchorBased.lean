/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoBlog
import DemoSite.Categories

open Lean.MessageSeverity

open Verso Genre Blog
open Verso.Code.External
open DemoSite

set_option verso.exampleProject "examples/website-examples"
set_option verso.exampleModule "AnchorExamples"

set_option pp.rawOnError true

#doc (Post) "Anchor-Based Examples from Subprojects" =>

%%%
authors := ["Fictional Author", "Another Fictional Author"]
date := {year := 2024, month := 3, day := 5}
categories := [examples, other]
%%%

This post demonstrates mixing highlighted examples from multiple Lean versions using anchor projects.
In these projects, examples are selected using specially-formatted comments, and don't need to match up with syntax boundaries.

# Foo

Here's a tree:

```anchor t
def t : Tree Nat :=
  .branch (.branch .leaf 1 .leaf) 2 (.branch (.branch .leaf 3 .leaf) 4 .leaf)
```

And here's just part of its definition:
```anchor tDef
  .branch (.branch .leaf 1 .leaf) 2 (.branch (.branch .leaf 3 .leaf) 4 .leaf)
```

It's left branch is {anchorTerm tDef}`.branch .leaf 1 .leaf` which includes a reference to {anchorName tDef}`.leaf`.

Checking types works too:
```anchor tflip
#check Tree.flip
```
```anchorInfo tflip
Tree.flip.{u_1} {α : Type u_1} (a✝ : Tree α) : Tree α
```
