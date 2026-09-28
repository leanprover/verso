/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
import Verso
import VersoManual

namespace Verso.Integration.Escape

open Verso Genre Manual InlineLean

--------------------

#docs (Manual) doc "Some code" :=
:::::::

%%%
authors := ["A robot"]
%%%

We need to check that closed braces (`]`) can appear inside item descriptions.

: As regular text: \]

  lorum ipsum \]

: As code: `]`

  * a `]`
  * b
  * c

: As math: $`]`

  lorum ipsum $`]`


  1. fish
  2. fruit
  3. bat

:::::::
