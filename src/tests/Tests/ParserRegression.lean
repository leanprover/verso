/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/
module
public import Verso
public import VersoManual

public section

/-
This is a test for https://github.com/leanprover/verso/issues/531
-/

open Verso Genre Manual

#docs (Manual) sample_part "Title of the Doc" :=
:::::::

%%%
shortTitle := "ShortTitle"
authors := ["Harry Q. Bovik"]
%%%

:::::::
