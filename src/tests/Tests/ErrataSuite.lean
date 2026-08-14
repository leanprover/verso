/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata
import all ErrataTests

/-- Errata's own tests, gathered so that a driver outside the module system can run them. -/
public def errataTests : Array Errata.TestEntry := getAllTests% "verso" ErrataTests
