/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Plausible
public meta import Verso.Theme.Color
public meta import Tests.Arbitrary

/-!
Unit and property tests for the accessibility predicates and checks in `Verso.Theme.Color.Accessibility`.
-/

open Plausible Gen Arbitrary Shrinkable
open Verso Verso.Theme Verso.Theme.Color

meta section

/-- The Okabe-Ito colorblind-safe palette, used to validate the distinguishability threshold. -/
def okabeIto : Array (String × Color) := #[
  ("black", color%#000000),
  ("orange", color%#e69f00),
  ("sky blue", color%#56b4e9),
  ("bluish green", color%#009e73),
  ("yellow", color%#f0e442),
  ("blue", color%#0072b2),
  ("vermillion", color%#d55e00),
  ("reddish purple", color%#cc79a7),
]

/-! ## Unit tests on curated palettes -/

-- A high-contrast pair (black on white) passes the text contrast check.
/-- info: true -/
#guard_msgs in
#eval (contrastIssues textContrastThreshold "black on white" .black .white).isEmpty

-- A low-contrast pair (gray on white, ratio ≈ 3.95) fails the text contrast check.
/-- info: false -/
#guard_msgs in
#eval (contrastIssues textContrastThreshold "gray on white" .gray .white).isEmpty

-- A nearly-opaque (99%) black composited over white is essentially black, so it passes easily.
/-- info: true -/
#guard_msgs in
#eval (contrastIssues textContrastThreshold "99% black on white" (color%#000000fc) .white).isEmpty

-- A half-transparent black over white composites to mid-gray, which fails the text threshold.
/-- info: false -/
#guard_msgs in
#eval (contrastIssues textContrastThreshold "50% black on white" (color%#00000080) .white).isEmpty

-- A translucent background cannot be contrast-checked: the effective backdrop is unknown.
/-- info: false -/
#guard_msgs in
#eval (contrastIssues textContrastThreshold "black on translucent" .black (color%#ffffff80)).isEmpty

-- A red and a green of matched lightness collapse together under deuteranopia (ΔE ≈ 2.1).
/-- info: false -/
#guard_msgs in
#eval (colorblindIssues distinguishableThreshold #[("red", color%#e60000), ("green", color%#00a000)]).isEmpty

-- Okabe-Ito blue and orange stay distinct under every dichromacy.
/-- info: true -/
#guard_msgs in
#eval (colorblindIssues distinguishableThreshold #[("blue", color%#0072b2), ("orange", color%#e69f00)]).isEmpty

-- The whole colorblind-safe Okabe-Ito palette passes the distinguishability check.
/-- info: true -/
#guard_msgs in
#eval (colorblindIssues distinguishableThreshold okabeIto).isEmpty

/-! ## Property tests -/

open scoped Plausible.Decorations in
def testProp
    (p : Prop) (cfg : Configuration := {})
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] :
    IO (TestResult p') :=
  Testable.checkIO p' (cfg := cfg)

/-- Contrast is monotone in the threshold: passing at 4.5 implies passing at 3.0. -/
def testContrastMonotone := testProp <| ∀ (fg bg : Color),
  !meetsContrast 4.5 fg bg || meetsContrast 3.0 fg bg

/-- When the contrast check reports no problem, the composited foreground meets the contrast. -/
def testNoContrastIssueMeansMeets := testProp <| ∀ (fg bg : Color),
  !(contrastIssues 4.5 "pair" fg bg).isEmpty || meetsContrast 4.5 (over fg bg) bg

open Lean (Name)

def colorAccessibilityTests : List (Name × (Σ p, IO <| TestResult p)) := [
  (`testContrastMonotone, ⟨_, testContrastMonotone⟩),
  (`testNoContrastIssueMeansMeets, ⟨_, testNoContrastIssueMeansMeets⟩),
]

public def runColorAccessibilityTests : IO Nat := do
  let mut failures := 0
  for (name, test) in colorAccessibilityTests do
    IO.print s!"{name}: "
    let res ← test.2
    IO.println res
    unless res matches .success .. do
      failures := failures + 1
  return failures
