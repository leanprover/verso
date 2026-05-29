/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Verso.Color.Types

set_option linter.missingDocs true
set_option doc.verso true

/-!
Color math for accessibility checking, using the following:

* Relative luminance and contrast ratio, from WCAG 2.1 ([relative
  luminance](https://www.w3.org/TR/WCAG21/#dfn-relative-luminance), [contrast
  ratio](https://www.w3.org/TR/WCAG21/#dfn-contrast-ratio)). A theme has to keep text readable
  against its background, and the WCAG contrast ratio is the accepted way to measure that.

* Color-vision-deficiency simulation, using the Brettel, Viénot & Mollon (1997) dichromacy method as
  reproduced by [libDaltonLens](https://github.com/DaltonLens/libDaltonLens). Brettel 1997 is used
  for all three dichromacies because the simpler Viénot 1999 single-matrix variant is inaccurate for
  tritanopia. Simulating how a palette looks to a color-blind reader lets the checker catch colors
  that collapse together and stop carrying meaning.

* Color difference, using CIEDE2000 (Sharma, Wu & Dalal 2005, "The CIEDE2000 color-difference
  formula"; [reference implementation and test
  data](https://hajim.rochester.edu/ece/sites/gsharma/ciede2000/)). It is a perceptually uniform
  measure of how distinct two colors look, used to decide whether two theme colors stay far enough
  apart, including under the simulations above.

All channels convert to {name}`Float` at the boundary (`/255`) and the math runs in {name}`Float`;
the {name (full := Verso.Color)}`Color` type itself stays byte-exact.
-/

namespace Verso

namespace Color

private def pi : Float := 3.141592653589793

private def fmin (a b : Float) : Float := if a < b then a else b
private def fmax (a b : Float) : Float := if a > b then a else b
private def clamp01 (v : Float) : Float := fmax 0.0 (fmin 1.0 v)

private def channelToFloat (x : UInt8) : Float := x.toNat.toFloat / 255.0

/-- Quantizes a {lit}`[0, 1]` channel back to a byte, rounding to nearest and clamping. -/
private def floatToChannel (v : Float) : UInt8 :=
  (Nat.min 255 ((clamp01 v * 255.0 + 0.5).toUInt64.toNat)).toUInt8

/--
The sRGB electro-optical transfer function: decodes a gamma-encoded {lit}`[0, 1]` channel to
linear-light. WCAG 2.1 and the sRGB standard use the {lit}`0.04045` threshold and the
{lit}`((c + 0.055) / 1.055) ^ 2.4` curve.
-/
private def srgbToLinear (c : Float) : Float :=
  if c < 0.04045 then c / 12.92
  else Float.pow ((c + 0.055) / 1.055) 2.4

/--
The inverse of {name}`srgbToLinear`: encodes a linear-light value back to a gamma-encoded
{lit}`[0, 1]` channel (clamping out-of-gamut values).
-/
private def linearToSrgb (v : Float) : Float :=
  if v ≤ 0.0 then 0.0
  else if v ≥ 1.0 then 1.0
  else if v < 0.0031308 then v * 12.92
  else Float.pow v (1.0 / 2.4) * 1.055 - 0.055

/--
The WCAG 2.1 relative luminance of a color, in {lit}`[0, 1]`. The alpha channel is ignored;
luminance is defined for opaque colors. Coefficients are the sRGB/Rec.709 luminance weights.
-/
public def relativeLuminance : Color → Float
  | .rgba r g b _ =>
    let rl := srgbToLinear (channelToFloat r)
    let gl := srgbToLinear (channelToFloat g)
    let bl := srgbToLinear (channelToFloat b)
    0.2126 * rl + 0.7152 * gl + 0.0722 * bl

/--
The WCAG 2.1 contrast ratio between two colors, in {lit}`[1, 21]`. The luminances are ordered by
max/min, so the ratio is symmetric in its arguments.
-/
public def contrastRatio (c1 c2 : Color) : Float :=
  let l1 := relativeLuminance c1
  let l2 := relativeLuminance c2
  (fmax l1 l2 + 0.05) / (fmin l1 l2 + 0.05)

/-- A type of color vision deficiency (dichromacy). -/
public inductive CVD where
  | protanopia
  | deuteranopia
  | tritanopia
deriving DecidableEq, Repr

/-- A row-major 3x3 matrix in linear RGB. -/
private abbrev Mat3 := Float × Float × Float × Float × Float × Float × Float × Float × Float

private def applyMat3 (m : Mat3) (r g b : Float) : Float × Float × Float :=
  let (m00, m01, m02, m10, m11, m12, m20, m21, m22) := m
  (m00 * r + m01 * g + m02 * b, m10 * r + m11 * g + m12 * b, m20 * r + m21 * g + m22 * b)

/--
The Brettel, Viénot & Mollon (1997) simulation parameters for a dichromacy: two linear-RGB matrices,
one per half-plane of the dichromat's reduced gamut, and the separation plane normal (also in linear
RGB) that selects between them. Each matrix's rows sum to one, so the gray axis is preserved. Values
from libDaltonLens (https://github.com/DaltonLens/libDaltonLens).
-/
private def brettelParams : CVD → Mat3 × Mat3 × (Float × Float × Float)
  | .protanopia =>
    ((0.14980, 1.19548, -0.34528, 0.10764, 0.84864, 0.04372, 0.00384, -0.00540, 1.00156),
     (0.14570, 1.16172, -0.30742, 0.10816, 0.85291, 0.03892, 0.00386, -0.00524, 1.00139),
     (0.00048, 0.00393, -0.00441))
  | .deuteranopia =>
    ((0.36477, 0.86381, -0.22858, 0.26294, 0.64245, 0.09462, -0.02006, 0.02728, 0.99278),
     (0.37298, 0.88166, -0.25464, 0.25954, 0.63506, 0.10540, -0.01980, 0.02784, 0.99196),
     (-0.00281, -0.00611, 0.00892))
  | .tritanopia =>
    ((1.01277, 0.13548, -0.14826, -0.01243, 0.86812, 0.14431, 0.07589, 0.80500, 0.11911),
     (0.93678, 0.18979, -0.12657, 0.06154, 0.81526, 0.12320, -0.37562, 1.12767, 0.24796),
     (0.03901, -0.02788, -0.01113))

/--
Simulates how a color appears to someone with the given color vision deficiency, using the Brettel
1997 method: decode sRGB to linear light, pick the half-plane matrix whose side of the separation
plane the color is on, apply it, then re-encode and quantize.
-/
public def dichromacy (cvd : CVD) : Color → Color
  | .rgba r g b a =>
    let rl := srgbToLinear (channelToFloat r)
    let gl := srgbToLinear (channelToFloat g)
    let bl := srgbToLinear (channelToFloat b)
    let (plane1, plane2, n0, n1, n2) := brettelParams cvd
    let m := if rl * n0 + gl * n1 + bl * n2 ≥ 0.0 then plane1 else plane2
    let (rl', gl', bl') := applyMat3 m rl gl bl
    .rgba (floatToChannel (linearToSrgb rl')) (floatToChannel (linearToSrgb gl'))
      (floatToChannel (linearToSrgb bl')) a

/-! # CIELAB color difference (CIEDE2000) -/

/--
Converts a color to CIELAB ({lit}`L*`, {lit}`a*`, {lit}`b*`) under the D65 white point, ignoring
alpha.
-/
private def toLab : Color → Float × Float × Float
  | .rgba r g b _ =>
    -- sRGB → linear → CIE XYZ (D65), the standard sRGB matrix.
    let rl := srgbToLinear (channelToFloat r)
    let gl := srgbToLinear (channelToFloat g)
    let bl := srgbToLinear (channelToFloat b)
    let x := 0.4124564 * rl + 0.3575761 * gl + 0.1804375 * bl
    let y := 0.2126729 * rl + 0.7151522 * gl + 0.0721750 * bl
    let z := 0.0193339 * rl + 0.1191920 * gl + 0.9503041 * bl
    -- XYZ → L*a*b* with the D65 reference white.
    let f := fun t =>
      if t > 0.008856451679035631 then Float.pow t (1.0 / 3.0)
      else 7.787037037037035 * t + 16.0 / 116.0
    let fx := f (x / 0.95047)
    let fy := f (y / 1.00000)
    let fz := f (z / 1.08883)
    (116.0 * fy - 16.0, 500.0 * (fx - fy), 200.0 * (fy - fz))

/--
The CIEDE2000 color difference ΔE₀₀ between two CIELAB colors, each given as {lit}`L*`, {lit}`a*`,
{lit}`b*`. Non-negative, symmetric, and zero for equal inputs. Implements the formulation of Sharma,
Wu & Dalal (2005), "The CIEDE2000 color-difference formula", with `kL = kC = kH = 1`. Factored out
of the color-level difference so it can be validated directly against Sharma's published Lab test
vectors (the test suite reaches it through `import all`).
-/
private def deltaE2000 (l1 a1 b1 l2 a2 b2 : Float) : Float := Id.run do
  let rad := fun d => d * pi / 180.0
  let deg := fun r => r * 180.0 / pi
  -- atan2 in degrees, in [0, 360).
  let atan2deg := fun y x =>
    let a := deg (Float.atan2 y x)
    if a < 0.0 then a + 360.0 else a
  let cosd := fun d => Float.cos (rad d)
  let sind := fun d => Float.sin (rad d)
  let pow7 := fun (t : Float) => Float.pow t 7.0
  let c25_7 := pow7 25.0
  let cstar1 := Float.sqrt (a1 * a1 + b1 * b1)
  let cstar2 := Float.sqrt (a2 * a2 + b2 * b2)
  let cbar := (cstar1 + cstar2) / 2.0
  let g := 0.5 * (1.0 - Float.sqrt (pow7 cbar / (pow7 cbar + c25_7)))
  let a1' := (1.0 + g) * a1
  let a2' := (1.0 + g) * a2
  let c1' := Float.sqrt (a1' * a1' + b1 * b1)
  let c2' := Float.sqrt (a2' * a2' + b2 * b2)
  let h1' := if a1' == 0.0 && b1 == 0.0 then 0.0 else atan2deg b1 a1'
  let h2' := if a2' == 0.0 && b2 == 0.0 then 0.0 else atan2deg b2 a2'
  let dL' := l2 - l1
  let dC' := c2' - c1'
  let dh' :=
    if c1' * c2' == 0.0 then 0.0
    else if (h2' - h1') > 180.0 then h2' - h1' - 360.0
    else if (h2' - h1') < -180.0 then h2' - h1' + 360.0
    else h2' - h1'
  let dH' := 2.0 * Float.sqrt (c1' * c2') * sind (dh' / 2.0)
  let lbar' := (l1 + l2) / 2.0
  let cbar' := (c1' + c2') / 2.0
  let hbar' :=
    if c1' * c2' == 0.0 then h1' + h2'
    else if (fmax h1' h2' - fmin h1' h2') ≤ 180.0 then (h1' + h2') / 2.0
    else if (h1' + h2') < 360.0 then (h1' + h2' + 360.0) / 2.0
    else (h1' + h2' - 360.0) / 2.0
  let t := 1.0 - 0.17 * cosd (hbar' - 30.0) + 0.24 * cosd (2.0 * hbar')
    + 0.32 * cosd (3.0 * hbar' + 6.0) - 0.20 * cosd (4.0 * hbar' - 63.0)
  let dtheta := 30.0 * Float.exp (-(((hbar' - 275.0) / 25.0) * ((hbar' - 275.0) / 25.0)))
  let rc := 2.0 * Float.sqrt (pow7 cbar' / (pow7 cbar' + c25_7))
  let sl := 1.0 + (0.015 * (lbar' - 50.0) * (lbar' - 50.0))
    / Float.sqrt (20.0 + (lbar' - 50.0) * (lbar' - 50.0))
  let sc := 1.0 + 0.045 * cbar'
  let sh := 1.0 + 0.015 * cbar' * t
  let rt := -(sind (2.0 * dtheta)) * rc
  let termL := dL' / sl
  let termC := dC' / sc
  let termH := dH' / sh
  return Float.sqrt (fmax 0.0 (termL * termL + termC * termC + termH * termH + rt * termC * termH))

/--
The CIEDE2000 color difference ΔE₀₀ between two colors, each first converted to CIELAB under the D65
white point. Non-negative, symmetric, and zero for equal colors.
-/
public def deltaE (c1 c2 : Color) : Float :=
  let (l1, a1, b1) := toLab c1
  let (l2, a2, b2) := toLab c2
  deltaE2000 l1 a1 b1 l2 a2 b2
