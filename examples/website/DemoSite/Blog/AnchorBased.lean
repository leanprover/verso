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
def someTree : Tree Nat :=
  .branch (.branch .leaf 1 .leaf) 2 (.branch (.branch .leaf 3 .leaf) 4 .leaf)
```

And here's just part of its definition:
```anchor tDef
  .branch (.branch .leaf 1 .leaf) 2 (.branch (.branch .leaf 3 .leaf) 4 .leaf)
```

It's left branch is {anchorTerm tDef}`.branch .leaf 1 .leaf` which includes a reference to {anchorName tDef}`.leaf`.

Including output works:
```anchor tflip
#eval someTree.flip
```
```anchorInfo tflip
Tree.branch
  (Tree.branch (Tree.leaf) 4 (Tree.branch (Tree.leaf) 3 (Tree.leaf)))
  2
  (Tree.branch (Tree.leaf) 1 (Tree.leaf))
```

As does proofs and parts of proofs:
```anchor proof1
theorem Tree.flip_flip_eq_id : flip ∘ flip = (id : Tree α → Tree α) := by
  funext t
  induction t with
  | leaf => rfl
  | branch l v r ih1 ih2 =>
    simp_all [flip]
```
Focusing on a branch:
```anchor proof1a
  | branch l v r ih1 ih2 =>
    simp_all [flip]
```
Or just one part:
```anchorTerm proof1a
branch l v r ih1 ih2
```
