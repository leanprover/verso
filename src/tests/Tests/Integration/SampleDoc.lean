/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/
import Verso
import VersoManual

namespace Verso.Integration.SampleDoc

open Verso Genre Manual

--------------------

/-- This is a docstring.

Here's some more text with a `code inline` in it.
Here's when a `code inline`
occurs right before a line break.

And then here's a paragraph break.
-/
def sample_constant := Unit

#docs (Manual) doc "Title of the Doc" :=
:::::::

%%%
shortTitle := "ShortTitle"
authors := ["Harry Q. Bovik"]
%%%

{docstring sample_constant}

Here is a test of `escaping of things like \TeX in code inlines`
:::::::

end Verso.Integration.SampleDoc
