/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
A test that this module marks with `attribute [test]` and another module declares. The test's file
is this module's, and its line is its declaration's.
-/
module

public import ErrataTests.Defaults.Helper

public section

namespace ErrataTests.Defaults

attribute [test] testMarkedElsewhere
