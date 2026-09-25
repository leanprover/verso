/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata

open Errata

/-- A test in a module that fails to build. -/
@[test]
def unbuildable : Test := pure ()

/-- A definition with a type error, which makes building this module fail. -/
def broken : Nat := "not a number"
