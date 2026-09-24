/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The Errata runner, which the driver starts with the configuration it wrote and the user's options.
-/
module

public import Errata.RunnerMain

/-- Runs the tests that the configuration names. -/
public def main (args : List String) : IO UInt32 :=
  Errata.Runner.main args
