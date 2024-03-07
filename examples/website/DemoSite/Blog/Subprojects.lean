import Verso.Genre.Blog
import DemoSite.Categories
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

They can be flipped around:

{leanCommand examples Examples.Basic.Tree.flip}

And subterms can be included: {leanTerm examples}`Examples.Basic.Tree.flip.flopped`.

We can even prove things about them:

{leanCommand examples Examples.proof}

And use old syntax:

{leanCommand examples Examples.oldterm}

Version is:

{leanCommand examples Examples.version}

that is,
```leanOutput Examples.version
"4.5.0"
```
