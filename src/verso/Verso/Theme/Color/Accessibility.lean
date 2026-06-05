/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Verso.Theme.Color.Types
public import Verso.Theme.Color.Math

set_option linter.missingDocs true
set_option doc.verso true

/-!
This module contains genre-neutral accessibility predicates and checks built on the color math:

 * WCAG contrast

 * CIEDE2000 distinguishability (including under simulated color vision deficiency)

-/

namespace Verso.Theme

namespace Color

/-- The kind of accessibility problem found, so a caller can route each to its own severity. -/
public inductive IssueKind where
  | contrast
  | colorblind
deriving DecidableEq, Repr

/--
An accessibility problem found while checking a set of colors. It carries no severity; the caller
maps {name}`IssueKind` to a severity. The offending colors are recorded for error messages.
-/
public structure Issue where
  /-- Whether this is a contrast or a color-vision-deficiency problem. -/
  kind : IssueKind
  /-- A human-readable description of the problem. -/
  message : String
  /-- The colors involved, for inclusion in error messages. -/
  offending : Array Color := #[]

/-- The WCAG AA contrast threshold for normal-size text. -/
public def textContrastThreshold : Float := 4.5

/-- The WCAG AA contrast threshold for large text and user-interface components. -/
public def largeContrastThreshold : Float := 3.0

/--
The CIEDE2000 ΔE above which two colors count as distinguishable. Set in the "clearly perceptible"
range: high enough to be a real difference, low enough not to flag the colorblind-safe Okabe-Ito
palette (which stays above it under all three dichromacies).
-/
public def distinguishableThreshold : Float := 5.0

/-- Whether a foreground on a background meets the given WCAG contrast ratio. -/
public def meetsContrast (threshold : Float) (fg bg : Color) : Bool :=
  contrastRatio fg bg ≥ threshold

/-- Whether two colors differ by at least the given threshold in CIEDE2000 ΔE. -/
public def distinguishable? (threshold : Float) (c1 c2 : Color) : Bool :=
  deltaE c1 c2 ≥ threshold

/-- Whether a color is fully opaque. Contrast can only be judged for opaque colors. -/
public def isOpaque : Color → Bool
  | .rgba _ _ _ a => a == 255

/--
Composites a foreground over a background using the foreground's alpha (straight alpha in sRGB,
matching how a browser paints translucent content on a solid background). The result is opaque; the
background's own alpha is ignored.
-/
public def over (fg bg : Color) : Color :=
  match fg, bg with
  | .rgba rf gf bf af, .rgba rb gb bb _ =>
    let a := af.toNat.toFloat / 255.0
    let mix (f b : UInt8) : UInt8 :=
      .ofNat (Nat.min 255 ((a * f.toNat.toFloat + (1.0 - a) * b.toNat.toFloat + 0.5).toUInt64.toNat))
    .rgba (mix rf rb) (mix gf gb) (mix bf bb) 255

private def cvdName : CVD → String
  | .protanopia => "protanopia"
  | .deuteranopia => "deuteranopia"
  | .tritanopia => "tritanopia"

/--
Checks that {name}`fg` has enough contrast against {name}`bg` for {name}`threshold`. A translucent
{name}`fg` is first composited over {name}`bg` (with {name}`over`), since that is the color actually
seen. The background must be opaque, though: contrast against a translucent background depends on an
unknown backdrop, so a non-opaque {name}`bg` is itself reported as a problem. {name}`description`
names the pair in any issue.
-/
public def contrastIssues (threshold : Float) (description : String) (fg bg : Color) : Array Issue :=
  if !isOpaque bg then
    #[{ kind := .contrast,
        message := s!"{description}: contrast cannot be judged because the background is not opaque",
        offending := #[bg] }]
  else
    let seen := over fg bg
    if meetsContrast threshold seen bg then
      #[]
    else
      #[{ kind := .contrast,
          message := s!"{description}: contrast ratio {contrastRatio seen bg} is below {threshold}",
          offending := #[fg, bg] }]

/--
Checks that the given named colors stay mutually distinguishable under each of the three
dichromacies. Reports a {name (full := IssueKind.colorblind)}`colorblind` issue for any pair that
collapses (ΔE below {name}`threshold`) under some simulation.

Pairs that are already identical in normal vision are skipped: the theme is not relying on color
to distinguish them, so a color-vision-deficient reader is in no worse a position than a
normal-vision one. Such pairs typically encode their distinction through weight or style (e.g. a
bold keyword versus an italic variable, both black).
-/
public def colorblindIssues (threshold : Float) (colors : Array (String × Color)) : Array Issue := Id.run do
  let mut out := #[]
  for i in [0:colors.size] do
    for j in [i + 1:colors.size] do
      let (n1, c1) := colors[i]!
      let (n2, c2) := colors[j]!
      if c1 == c2 then continue
      for cvd in [CVD.protanopia, CVD.deuteranopia, CVD.tritanopia] do
        unless distinguishable? threshold (dichromacy cvd c1) (dichromacy cvd c2) do
          out := out.push
            { kind := .colorblind,
              message := s!"{n1} and {n2} are indistinguishable under {cvdName cvd}",
              offending := #[c1, c2] }
  return out
