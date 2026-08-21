/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen

A module holding a test, for checks of test discovery itself. Its name extends
`ErrataTests.Fixture`'s name, so it lies below that module as well as below itself.
-/
module

public import Errata

open Errata

/-- A test in the nested fixture module. -/
@[test]
def subFixtureTest : Bool := true
