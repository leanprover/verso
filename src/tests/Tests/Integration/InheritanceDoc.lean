/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/
import Verso
import VersoManual

namespace Verso.Integration.InheritanceDoc

open Verso Genre Manual

/--
Documentation for BarExtended
-/
structure BarExtended where
  /--
  Documentation for barField1
  -/
  barField1 : Bool
  /--
  Documentation for barField2
  -/
  barField2 : Unit

/--
Documentation for FooExtends
-/
structure FooExtends extends BarExtended where
  /--
  Documentation for fooField1
  -/
 fooField1 : Nat
  /--
  Documentation for fooField2
  -/
 fooField2 : String

#docs (Manual) doc "Title of the Doc" :=
:::::::

%%%
shortTitle := "ShortTitle"
authors := ["Harry Q. Bovik"]
%%%

{docstring FooExtends}

:::::::

end Verso.Integration.InheritanceDoc
