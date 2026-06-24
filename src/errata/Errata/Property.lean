/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module

public import Errata.TestM
public import Plausible
public import Plausible.ArbitraryFueled

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

open Plausible

open scoped Plausible.Decorations in
/-- Checks a property with Plausible, failing with the counterexample if it is falsified. -/
def property (p : Prop) (cfg : Configuration := {})
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : TestM Unit := do
  let ctx ← read
  let cfg := { cfg with
    quiet := true,
    randomSeed := if ctx.seed == 0 then cfg.randomSeed else some ctx.seed }
  match ← Testable.checkIO p' (cfg := cfg) with
  | .success _ => pure ()
  | .gaveUp n => fail s!"property gave up after discarding {n} cases"
  | .failure _ counterExample _ =>
    fail "property falsified" (detail? := some ("\n".intercalate counterExample))
