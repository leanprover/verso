/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata

open Errata

/-- What the test in this module writes. -/
private def greeting : String := "from TwinB"

/-- A test whose name and source are the same as those of the test in the other twin module. -/
@[test]
def twin : Test := IO.println greeting
