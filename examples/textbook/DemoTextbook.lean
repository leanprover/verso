/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Genre.Manual
import DemoTextbook.Exts.Index
import DemoTextbook.Exts.Exercises

open Verso.Genre Manual
open DemoTextbook.Exts (index theIndex see seeAlso lean)

set_option pp.rawOnError true

#doc (Manual) "A Textbook" =>

%%%
authors := ["David Thrane Christiansen"]
%%%

{index}[example]
Here's an example project showing how to build a certain kind of textbook with Verso.

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

# Exercises

This book format supports Lean examples {index subterm:="embedded Lean"}[example] and exercises.

```lean
def five : Nat := 5
```

```lean
theorem five_eq_5 : five = 5 := by
  -- !! begin solution
  skip; skip
  skip
  have := True.intro
  skip; sorry
  -- !! end solution
  -- !! begin exercise
  have : "a" = "a" := by rfl
  rfl
  -- !! end exercise
```

# Index
%%%
number := false
%%%

{theIndex}
