/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Declarations that `ErrataTests.Defaults` marks or calls from another module: a function that a
setting's default calls, a setting that it marks with `attribute [setting]`, and a test that it
marks with `attribute [test]`.
-/
module

public import Errata

open Errata

public section

namespace ErrataTests.Defaults

/-- The default that a setting of another module computes. -/
def helperDefault (n : Nat) : String := s!"n{n}"

/-- A setting that another module marks. -/
@[expose]
def markedElsewhere : Setting where
  type := String
  fromString s := some s
  default? := some "d"

/-- A test that another module marks. -/
def testMarkedElsewhere : Test := pure ()
