/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Genre.Blog
import DemoSite.Categories
import Lean

open Lean.MessageSeverity

open Verso Genre Blog
open DemoSite



set_option pp.rawOnError true

#doc (Post) "Examples from Subprojects" =>

%%%
authors := ["Fictional Author", "Another Fictional Author"]
date := {year := 2024, month := 3, day := 5}
categories := [examples, other]
%%%

This post demonstrates mixing highlighted examples from multiple Lean versions.

{leanExampleProject examples "examples/website-examples"}

# Foo

Here's a tree:

{leanCommand examples Examples.Basic.Tree}

They can be flipped around with {leanTerm examples}`FLIP`:

{leanCommand examples Examples.Basic.Tree.flip}

And subterms can be included: {leanTerm examples}`Examples.Basic.Tree.flip.flopped`.

We can even prove things about them:

{leanCommand examples Examples.proof}

And use old syntax:

{leanCommand examples Examples.oldterm}

Version is:

{leanCommand examples Examples.version}

that is,
```leanOutput Examples.version severity := information
"4.5.0"
```
