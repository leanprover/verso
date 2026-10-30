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

set_option verso.exampleProject "test-projects/website-examples"
set_option verso.exampleModule "Examples"

set_option pp.rawOnError true

#doc (Post) "Examples from Subprojects" =>

%%%
authors := ["Fictional Author", "Another Fictional Author"]
date := {year := 2024, month := 3, day := 5}
categories := [examples, other]
%%%

This post demonstrates mixing highlighted examples from multiple Lean versions.
The example project is made up of ordinary Lean modules, with examples indicated via `-- ANCHOR:` comments.

{leanExampleModule exampleMod "test-projects/website-examples" Examples}


# Foo

Here's a tree:

```anchor Tree (module := Examples.Basic)
inductive Tree (α : Type u) : Type u where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)
```

They can be flipped around with {anchorName Tree.flip (module := Examples.Basic)}`Tree.flip`, also known as {anchorName Tree.flip (module := Examples.Basic) (show := FLIP)}`Tree.flip`:

```anchor Tree.flip (module := Examples.Basic)
def Tree.flip : Tree α → Tree α
  | .leaf => .leaf
  | .branch l v r =>
    .branch r.flip v l.flip
```

And subterms can be included: {anchorTerm flopped (module := Examples.Basic)}`.branch r.flip v l.flip`.

We can even prove things about them:

```anchor proof
theorem Tree.flip_flip_id (t : Tree α) : t.flip.flip = t := by
  induction t with
  | leaf => rfl
  | branch l v r ih1 ih2 =>
    simp only [flip]
    rw [ih1]; rw [ih2]

-- Show more tactic combinators and placement of proof states
theorem Tree.flip_flip_id' (t : Tree α) : t.flip.flip = t := by
  induction t
  case leaf => rfl
  next l v r ih1 ih2 =>
    simp only [flip]
    rw [ih1]; . rw [ih2]
```

And use old syntax:

```anchor oldterm
-- The old syntax:
def foo (n k : Nat) : Nat :=
  if n < k then
    1 + foo (n + 1) k
  else 0
termination_by k - n
```

Version is:

```anchor version
#eval Lean.versionString
```

that is,
```anchorInfo version
"4.31.0"
```

Output is compared modulo trailing whitespace:

```anchor basic
def t : Tree Nat := .branch (.branch .leaf 1 .leaf) 2 (.branch (.branch .leaf 3 .leaf) 4 .leaf)

example := t.flip

#eval t.flip

#check Tree.flip
```

```anchorInfo basic
Tree.branch
  (Tree.branch (Tree.leaf) 4 (Tree.branch (Tree.leaf) 3 (Tree.leaf)))
  2
  (Tree.branch (Tree.leaf) 1 (Tree.leaf))
```


Here's a name from the standard library, highlighted from an example in an anchor: {anchorName natRec}`Nat.rec`.

Here's a command included from a line number:

{leanCommandAt exampleMod 30}
