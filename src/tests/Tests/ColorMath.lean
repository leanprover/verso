/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Plausible
public meta import Verso.Theme.Color
import all Verso.Theme.Color.Math
public meta import Tests.Arbitrary

/-!
Unit and property tests for the color math in `Verso.Theme.Color.Math`.
-/

open Plausible Gen Arbitrary Shrinkable
open Verso Verso.Theme Verso.Theme.Color

meta section

/-- Approximate float equality to a tolerance. -/
def approx (ε a b : Float) : Bool := (a - b).abs ≤ ε

/-- Whether two colors' channels are all within `ε` of each other. -/
def channelsClose (ε : Nat) : Color → Color → Bool
  | .rgba r1 g1 b1 a1, .rgba r2 g2 b2 a2 =>
    let near (x y : UInt8) : Bool := (Int.ofNat x.toNat - Int.ofNat y.toNat).natAbs ≤ ε
    near r1 r2 && near g1 g2 && near b1 b2 && near a1 a2

instance : Arbitrary CVD where
  arbitrary := Gen.elements [.protanopia, .deuteranopia, .tritanopia] (by simp)

instance : Shrinkable CVD where
  shrink _ := []

/-! ## Unit tests on reference values -/

-- Relative luminance of black is 0 and of white is 1, so their contrast ratio is the maximal 21.
/-- info: (0.000000, 1.000000, 21.000000) -/
#guard_msgs in
#eval (relativeLuminance .black, relativeLuminance .white, contrastRatio .black .white)

-- ΔE is zero for equal colors and large for black vs. white.
/-- info: (0.000000, 100.000004) -/
#guard_msgs in
#eval (deltaE .black .black, deltaE .white .black)

-- Dichromacy simulation leaves the gray axis unchanged.
/-- info: (Verso.Theme.Color.rgba 128 128 128 255, Verso.Theme.Color.rgba 128 128 128 255, Verso.Theme.Color.rgba 128 128 128 255) -/
#guard_msgs in
#eval (dichromacy .protanopia .gray, dichromacy .deuteranopia .gray, dichromacy .tritanopia .gray)

-- Red and green, far apart normally, collapse closer together under deuteranopia.
/-- info: true -/
#guard_msgs in
#eval deltaE (dichromacy .deuteranopia .red) (dichromacy .deuteranopia .green) < deltaE .red .green

/-! ## Property tests -/

open scoped Plausible.Decorations in
def testProp
    (p : Prop) (cfg : Configuration := {})
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] :
    IO (TestResult p') :=
  Testable.checkIO p' (cfg := cfg)

/-- Relative luminance lies in [0, 1]. -/
def testLuminanceRange := testProp <| ∀ (c : Color),
  0.0 ≤ relativeLuminance c ∧ relativeLuminance c ≤ 1.000000001

/-- Raises a channel by `d`, saturating at 255. -/
private def raise (x d : UInt8) : UInt8 := UInt8.ofNat (Nat.min 255 (x.toNat + d.toNat))

/-- Raising any channel never lowers the relative luminance. -/
def testLuminanceMonotone := testProp <| ∀ (r g b d0 d1 d2 : UInt8),
  relativeLuminance (.rgba r g b 255)
    ≤ relativeLuminance (.rgba (raise r d0) (raise g d1) (raise b d2) 255) + 0.000000001

/-- Contrast ratio is symmetric. -/
def testContrastSymmetric := testProp <| ∀ (c d : Color),
  approx 0.000000001 (contrastRatio c d) (contrastRatio d c)

/-- Contrast ratio lies in [1, 21]. -/
def testContrastRange := testProp <| ∀ (c d : Color),
  0.999999999 ≤ contrastRatio c d ∧ contrastRatio c d ≤ 21.000000001

/-- A color has contrast ratio 1 with itself. -/
def testContrastSelf := testProp <| ∀ (c : Color),
  approx 0.000000001 (contrastRatio c c) 1.0

/-- ΔE is non-negative. -/
def testDeltaENonneg := testProp <| ∀ (c d : Color), deltaE c d ≥ 0.0

/-- ΔE is symmetric. -/
def testDeltaESymmetric := testProp <| ∀ (c d : Color),
  approx 0.0001 (deltaE c d) (deltaE d c)

/-- ΔE is zero for equal colors. -/
def testDeltaEZero := testProp <| ∀ (c : Color), approx 0.000001 (deltaE c c) 0.0

/-- Dichromacy maps the gray axis to itself (within one quantization step). -/
def testDichromacyGray := testProp <| ∀ (cvd : CVD) (v : UInt8),
  channelsClose 1 (dichromacy cvd (.rgba v v v 255)) (.rgba v v v 255)

/-- The alpha channel of a color. -/
private def alphaOf : Color → UInt8
  | .rgba _ _ _ a => a

/--
Dichromacy preserves the alpha channel.

It is *not* idempotent on the quantized, gamut-clamped `Color`: clipping a channel to 0 or 255
discards the exact projected point, so a second pass can drift. Idempotence holds only for the
continuous linear-light projection.
-/
def testDichromacyAlphaPreserved := testProp <| ∀ (cvd : CVD) (c : Color),
  alphaOf (dichromacy cvd c) == alphaOf c

/-- Relative luminance ignores the alpha channel. -/
def testLuminanceIgnoresAlpha := testProp <| ∀ (r g b a : UInt8),
  relativeLuminance (.rgba r g b a) == relativeLuminance (.rgba r g b 255)

/-- Replaces a color's alpha channel with full opacity. -/
private def «opaque» : Color → Color
  | .rgba r g b _ => .rgba r g b 255

/-- Contrast ratio ignores the alpha channel. -/
def testContrastIgnoresAlpha := testProp <| ∀ (c1 c2 : Color),
  contrastRatio c1 c2 == contrastRatio («opaque» c1) («opaque» c2)

/-- ΔE ignores the alpha channel. -/
def testDeltaEIgnoresAlpha := testProp <| ∀ (c1 c2 : Color),
  deltaE c1 c2 == deltaE («opaque» c1) («opaque» c2)

/--
Deuteranopia collapses pure red and pure green toward each other: the simulated ΔE between
{lit}`(r, 0, 0)` and {lit}`(0, g, 0)` never exceeds the original ΔE (within a small numerical
tolerance for sRGB round-trip and 8-bit rounding).

`≤` rather than strict `<` because the degenerate `r = g = 0` case has both colors equal to
black and both ΔEs equal to zero. The strict inequality is exercised by the targeted
spot-check {Lean.Doc.name}`testDeuteranopiaRedGreenSpotCheck` below, which uses pure-saturated
red and green so the collapse is unambiguous.
-/
def testDeuteranopiaCollapsesRedGreen := testProp <| ∀ (r g : UInt8),
  let red : Color := .rgba r 0 0 255
  let green : Color := .rgba 0 g 0 255
  let simRed := dichromacy .deuteranopia red
  let simGreen := dichromacy .deuteranopia green
  -- A tiny tolerance absorbs sRGB encode-decode round-trip plus 8-bit rounding noise on the
  -- ΔE pipeline. Without it the inequality can flip by ~1e-3 at boundary inputs.
  deltaE simRed simGreen ≤ deltaE red green + 0.001

/--
Spot check: pure saturated red and pure saturated green are far apart normally but collapse
much closer together under deuteranopia. Asserts the simulated ΔE drops to less than half the
unsimulated one — well outside any quantization noise band, so the directionality of the
collapse is what the test actually exercises (where the bounded-form property
{Lean.Doc.name}`testDeuteranopiaCollapsesRedGreen` only asserts non-increase).
-/
def testDeuteranopiaRedGreenSpotCheck := testProp <|
  let red : Color := .rgba 255 0 0 255
  let green : Color := .rgba 0 255 0 255
  let simRed := dichromacy .deuteranopia red
  let simGreen := dichromacy .deuteranopia green
  deltaE simRed simGreen < deltaE red green / 2

open Lean (Name)

def colorMathTests : List (Name × (Σ p, IO <| TestResult p)) := [
  (`testLuminanceRange, ⟨_, testLuminanceRange⟩),
  (`testLuminanceMonotone, ⟨_, testLuminanceMonotone⟩),
  (`testContrastSymmetric, ⟨_, testContrastSymmetric⟩),
  (`testContrastRange, ⟨_, testContrastRange⟩),
  (`testContrastSelf, ⟨_, testContrastSelf⟩),
  (`testDeltaENonneg, ⟨_, testDeltaENonneg⟩),
  (`testDeltaESymmetric, ⟨_, testDeltaESymmetric⟩),
  (`testDeltaEZero, ⟨_, testDeltaEZero⟩),
  (`testDichromacyGray, ⟨_, testDichromacyGray⟩),
  (`testDichromacyAlphaPreserved, ⟨_, testDichromacyAlphaPreserved⟩),
  (`testLuminanceIgnoresAlpha, ⟨_, testLuminanceIgnoresAlpha⟩),
  (`testContrastIgnoresAlpha, ⟨_, testContrastIgnoresAlpha⟩),
  (`testDeltaEIgnoresAlpha, ⟨_, testDeltaEIgnoresAlpha⟩),
  (`testDeuteranopiaCollapsesRedGreen, ⟨_, testDeuteranopiaCollapsesRedGreen⟩),
  (`testDeuteranopiaRedGreenSpotCheck, ⟨_, testDeuteranopiaRedGreenSpotCheck⟩),
]

public def runColorMathTests : IO Nat := do
  let mut failures := 0
  for (name, test) in colorMathTests do
    IO.print s!"{name}: "
    let res ← test.2
    IO.println res
    unless res matches .success .. do
      failures := failures + 1
  return failures

/-!
## Source-backed simulation cases

`cvdReferenceVectors` are outputs of DaltonLens-Python's `Simulator_Brettel1997` (severity 1.0), the
reference implementation that libDaltonLens is validated against. Each row is
`(input, protanopia, deuteranopia, tritanopia)`. `dichromacy` is expected to match each within a
couple of byte units: the small difference comes from libDaltonLens's matrix coefficients being
rounded to five decimals, not from a different method. A large deviation would mean a transposed
matrix, wrong half-plane sign, wrong gamma direction, or swapped channels.
-/

def cvdReferenceVectors : List (Color × Color × Color × Color) := [
  (.rgba 0 0 0 255, .rgba 0 0 0 255, .rgba 0 0 0 255, .rgba 0 0 0 255),
  (.rgba 255 255 255 255, .rgba 254 254 254 255, .rgba 254 254 254 255, .rgba 254 254 254 255),
  (.rgba 128 128 128 255, .rgba 128 128 128 255, .rgba 128 128 128 255, .rgba 128 128 128 255),
  (.rgba 255 0 0 255, .rgba 106 90 13 255, .rgba 163 138 0 255, .rgba 254 0 78 255),
  (.rgba 0 128 0 255, .rgba 139 118 0 255, .rgba 120 103 17 255, .rgba 58 117 135 255),
  (.rgba 0 0 255 255, .rgba 0 54 254 255, .rgba 0 86 254 255, .rgba 0 95 134 255),
  (.rgba 255 255 0 255, .rgba 254 250 0 255, .rgba 254 242 21 255, .rgba 254 239 242 255),
  (.rgba 0 255 255 255, .rgba 238 242 254 255, .rgba 209 223 254 255, .rgba 73 248 254 255),
  (.rgba 255 0 255 255, .rgba 0 105 254 255, .rgba 101 160 251 255, .rgba 238 98 120 255),
  (.rgba 29 3 65 255, .rgba 0 13 65 255, .rgba 0 23 64 255, .rgba 14 21 23 255),
  (.rgba 220 20 60 255, .rgba 87 81 62 255, .rgba 139 121 49 255, .rgba 220 12 72 255),
  (.rgba 0 128 255 255, .rgba 0 129 254 255, .rgba 0 132 254 255, .rgba 0 147 185 255),
  (.rgba 217 163 130 255, .rgba 181 168 130 255, .rgba 191 176 128 255, .rgba 220 158 164 255),
  (.rgba 69 78 10 255, .rgba 88 75 9 255, .rgba 84 71 12 255, .rgba 75 72 73 255),
  (.rgba 19 4 44 255, .rgba 0 8 44 255, .rgba 0 15 43 255, .rgba 9 13 15 255),
  (.rgba 208 166 233 255, .rgba 144 174 233 255, .rgba 164 185 231 255, .rgba 198 176 178 255),
  (.rgba 128 155 248 255, .rgba 98 157 248 255, .rgba 107 160 247 255, .rgba 105 168 190 255),
  (.rgba 186 161 139 255, .rgba 171 163 139 255, .rgba 175 165 138 255, .rgba 188 157 160 255),
  (.rgba 143 239 71 255, .rgba 254 226 68 255, .rgba 237 207 80 255, .rgba 173 222 242 255),
  (.rgba 208 171 0 255, .rgba 200 172 0 255, .rgba 202 173 0 255, .rgba 217 159 165 255),
  (.rgba 100 219 141 255, .rgba 228 207 140 255, .rgba 204 189 144 255, .rgba 130 206 233 255),
  (.rgba 8 195 186 255, .rgba 185 185 185 255, .rgba 162 169 187 255, .rgba 60 188 223 255),
  (.rgba 216 44 22 255, .rgba 99 86 26 255, .rgba 142 121 0 255, .rgba 217 32 77 255),
  (.rgba 220 5 138 255, .rgba 43 82 138 255, .rgba 124 126 133 255, .rgba 215 46 82 255),
  (.rgba 20 76 123 255, .rgba 43 74 122 255, .rgba 38 73 123 255, .rgba 0 81 99 255),
  (.rgba 108 103 7 255, .rgba 118 101 6 255, .rgba 116 99 9 255, .rgba 114 96 97 255),
  (.rgba 1 31 2 255, .rgba 34 28 1 255, .rgba 28 23 3 255, .rgba 9 27 33 255),
  (.rgba 171 134 165 255, .rgba 129 139 165 255, .rgba 141 147 164 255, .rgba 167 138 141 255),
  (.rgba 65 157 195 255, .rgba 132 152 194 255, .rgba 119 144 195 255, .rgba 59 158 186 255),
  (.rgba 98 117 255 255, .rgba 0 124 254 255, .rgba 0 134 254 255, .rgba 34 141 169 255),
  (.rgba 206 251 97 255, .rgba 254 242 95 255, .rgba 254 229 102 255, .rgba 225 236 242 255),
  (.rgba 175 243 166 255, .rgba 254 234 165 255, .rgba 237 220 168 255, .rgba 192 232 249 255),
  (.rgba 215 176 180 255, .rgba 180 180 180 255, .rgba 190 187 179 255, .rgba 214 176 179 255),
  (.rgba 99 224 34 255, .rgba 244 210 28 255, .rgba 218 189 51 255, .rgba 140 207 231 255),
  (.rgba 148 184 216 255, .rgba 167 182 215 255, .rgba 162 179 216 255, .rgba 144 186 203 255),
  (.rgba 134 96 79 255, .rgba 107 100 79 255, .rgba 115 106 77 255, .rgba 135 93 97 255),
  (.rgba 108 124 184 255, .rgba 92 125 184 255, .rgba 96 127 183 255, .rgba 95 132 146 255),
  (.rgba 227 18 239 255, .rgba 0 96 239 255, .rgba 82 145 236 255, .rgba 210 94 111 255),
  (.rgba 136 91 172 255, .rgba 47 101 172 255, .rgba 82 114 171 255, .rgba 123 106 107 255),
  (.rgba 146 65 82 255, .rgba 78 79 82 255, .rgba 101 95 79 255, .rgba 145 65 77 255),
  (.rgba 184 152 129 255, .rgba 163 154 129 255, .rgba 169 159 128 255, .rgba 186 148 152 255),
  (.rgba 86 194 100 255, .rgba 206 183 99 255, .rgba 184 166 104 255, .rgba 116 181 204 255),
  (.rgba 84 227 67 255, .rgba 245 213 64 255, .rgba 217 190 77 255, .rgba 131 210 237 255),
  (.rgba 58 182 159 255, .rgba 178 173 158 255, .rgba 157 158 160 255, .rgba 83 175 203 255),
  (.rgba 12 21 96 255, .rgba 0 27 96 255, .rgba 0 34 95 255, .rgba 0 38 52 255),
  (.rgba 213 102 201 255, .rgba 74 125 201 255, .rgba 129 152 198 255, .rgba 203 120 130 255),
  (.rgba 81 61 202 255, .rgba 0 75 202 255, .rgba 0 92 201 255, .rgba 20 94 112 255),
  (.rgba 224 20 14 255, .rgba 95 81 21 255, .rgba 144 122 0 255, .rgba 225 0 71 255),
  (.rgba 171 86 146 255, .rgba 78 102 146 255, .rgba 112 121 144 255, .rgba 165 95 104 255),
  (.rgba 38 220 115 255, .rgba 231 206 113 255, .rgba 202 184 120 255, .rgba 103 205 237 255),
]

/-- The largest per-channel difference between two colors (ignoring alpha). -/
private def chanMaxDiff : Color → Color → Nat
  | .rgba r1 g1 b1 _, .rgba r2 g2 b2 _ =>
    let d (x y : UInt8) : Nat := (Int.ofNat x.toNat - Int.ofNat y.toNat).natAbs
    max (d r1 r2) <| max (d g1 g2) (d b1 b2)

/--
The greatest per-channel deviation of `dichromacy` from the DaltonLens reference, over all vectors
and all three deficiencies. Pinned so a regression (or a larger deviation than the matrix rounding
explains) fails the test.
-/
def cvdReferenceMaxDeviation : Nat :=
  cvdReferenceVectors.foldl (init := 0) fun acc (c, p, de, t) =>
    max acc <|
      max (chanMaxDiff (dichromacy .protanopia c) p) <|
        max (chanMaxDiff (dichromacy .deuteranopia c) de) (chanMaxDiff (dichromacy .tritanopia c) t)

-- `dichromacy` matches the DaltonLens reference across all 50 vectors and all three deficiencies. The
-- largest per-channel deviation is 7, for one tritanopia color (`rgba 81 61 202`) that sits near the
-- half-plane boundary, where the hard plane switch and the 5-decimal-rounded matrices interact; the
-- rest are within about 3. A transposed matrix, flipped half-plane sign, or wrong gamma direction
-- would push this far higher.
/-- info: 7 -/
#guard_msgs in
#eval cvdReferenceMaxDeviation

/-! ## CIEDE2000 against Sharma's published Lab vectors

`deltaE2000` (the CIELAB core of `deltaE`, reached via `import all`) is validated against the 34
test pairs from Sharma, Wu & Dalal (2005), Table 1, the canonical data for checking a CIEDE2000
implementation. These pairs deliberately exercise the hue-rotation and near-zero-chroma cases that
catch transcription errors the broad invariants miss. Values via the reference implementation at
https://github.com/gfiumara/CIEDE2000.
-/

def sharmaDeltaEVectors : List ((Float × Float × Float) × (Float × Float × Float) × Float) := [
  ((50.0, 2.6772, -79.7751), (50.0, 0.0, -82.7485), 2.0425),
  ((50.0, 3.1571, -77.2803), (50.0, 0.0, -82.7485), 2.8615),
  ((50.0, 2.8361, -74.0200), (50.0, 0.0, -82.7485), 3.4412),
  ((50.0, -1.3802, -84.2814), (50.0, 0.0, -82.7485), 1.0000),
  ((50.0, -1.1848, -84.8006), (50.0, 0.0, -82.7485), 1.0000),
  ((50.0, -0.9009, -85.5211), (50.0, 0.0, -82.7485), 1.0000),
  ((50.0, 0.0, 0.0), (50.0, -1.0, 2.0), 2.3669),
  ((50.0, -1.0, 2.0), (50.0, 0.0, 0.0), 2.3669),
  ((50.0, 2.4900, -0.0010), (50.0, -2.4900, 0.0009), 7.1792),
  ((50.0, 2.4900, -0.0010), (50.0, -2.4900, 0.0010), 7.1792),
  ((50.0, 2.4900, -0.0010), (50.0, -2.4900, 0.0011), 7.2195),
  ((50.0, 2.4900, -0.0010), (50.0, -2.4900, 0.0012), 7.2195),
  ((50.0, -0.0010, 2.4900), (50.0, 0.0009, -2.4900), 4.8045),
  ((50.0, -0.0010, 2.4900), (50.0, 0.0010, -2.4900), 4.8045),
  ((50.0, -0.0010, 2.4900), (50.0, 0.0011, -2.4900), 4.7461),
  ((50.0, 2.5000, 0.0), (50.0, 0.0, -2.5000), 4.3065),
  ((50.0, 2.5000, 0.0), (73.0, 25.0, -18.0), 27.1492),
  ((50.0, 2.5000, 0.0), (61.0, -5.0, 29.0), 22.8977),
  ((50.0, 2.5000, 0.0), (56.0, -27.0, -3.0), 31.9030),
  ((50.0, 2.5000, 0.0), (58.0, 24.0, 15.0), 19.4535),
  ((50.0, 2.5000, 0.0), (50.0, 3.1736, 0.5854), 1.0000),
  ((50.0, 2.5000, 0.0), (50.0, 3.2972, 0.0), 1.0000),
  ((50.0, 2.5000, 0.0), (50.0, 1.8634, 0.5757), 1.0000),
  ((50.0, 2.5000, 0.0), (50.0, 3.2592, 0.3350), 1.0000),
  ((60.2574, -34.0099, 36.2677), (60.4626, -34.1751, 39.4387), 1.2644),
  ((63.0109, -31.0961, -5.8663), (62.8187, -29.7946, -4.0864), 1.2630),
  ((61.2901, 3.7196, -5.3901), (61.4292, 2.2480, -4.9620), 1.8731),
  ((35.0831, -44.1164, 3.7933), (35.0232, -40.0716, 1.5901), 1.8645),
  ((22.7233, 20.0904, -46.6940), (23.0331, 14.9730, -42.5619), 2.0373),
  ((36.4612, 47.8580, 18.3852), (36.2715, 50.5065, 21.2231), 1.4146),
  ((90.8027, -2.0831, 1.4410), (91.1528, -1.6435, 0.0447), 1.4441),
  ((90.9257, -0.5406, -0.9208), (88.6381, -0.8985, -0.7239), 1.5381),
  ((6.7747, -0.2908, -2.4247), (5.8714, -0.0985, -2.2286), 0.6377),
  ((2.0776, 0.0795, -1.1350), (0.9033, -0.0636, -0.5514), 0.9082),
]

/--
The greatest absolute deviation of `deltaE2000` from Sharma's published ΔE₀₀, over all 34 vectors.
Sharma publishes four decimal places, so a correct implementation lands within rounding.
-/
def sharmaMaxDeviation : Float :=
  sharmaDeltaEVectors.foldl (init := 0.0) fun acc (lab1, lab2, exp) =>
    let (l1, a1, b1) := lab1
    let (l2, a2, b2) := lab2
    let d := (deltaE2000 l1 a1 b1 l2 a2 b2 - exp).abs
    if acc < d then d else acc

-- `deltaE2000` reproduces every Sharma reference value to within their published precision (four
-- decimals), confirming the CIEDE2000 formula is transcribed correctly (including the tricky
-- hue-rotation and near-zero-chroma cases).
/-- info: true -/
#guard_msgs in
#eval sharmaMaxDeviation < 0.0001
