/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Verso.Theme.Color.Types

set_option linter.missingDocs true
set_option doc.verso true

/-!
The pure Lean API for {name (full := Verso.Theme.Color)}`Color`: a small set of named colors, CSS and TeX
rendering, and parsing of hex color strings.
-/

namespace Verso.Theme.Color

/--
Constructs an opaque color.
-/
public def rgb (red green blue : UInt8) : Color := .rgba red green blue 255

/-- Opaque black. -/
public def black : Color := .rgb 0 0 0
/-- Opaque white. -/
public def white : Color := .rgb 255 255 255
/-- A medium gray, matching the CSS {lit}`gray` keyword ({lit}`#808080`). -/
public def gray : Color := .rgb 128 128 128
/-- Opaque red, matching the CSS {lit}`red` keyword ({lit}`#ff0000`). -/
public def red : Color := .rgb 255 0 0
/-- Opaque green, matching the CSS {lit}`green` keyword ({lit}`#008000`, not full-intensity {lit}`#00ff00`). -/
public def green : Color := .rgb 0 128 0
/-- Opaque blue, matching the CSS {lit}`blue` keyword ({lit}`#0000ff`). -/
public def blue : Color := .rgb 0 0 255
/-- Fully transparent (zero alpha). -/
public def transparent : Color := .rgba 0 0 0 0

private def hexDigit (upper : Bool) (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ((if upper then 'A' else 'a').toNat + (n - 10))

private def hexByte (upper : Bool) (b : UInt8) : String :=
  let n := b.toNat
  String.ofList [hexDigit upper (n / 16), hexDigit upper (n % 16)]

/--
Renders a color for CSS as lowercase hex: `#rrggbb` when fully opaque, otherwise `#rrggbbaa`. Using
hex for both keeps one format and maps the alpha byte exactly, with no decimal rounding.
-/
public def css : Color → String
  | .rgba r g b a =>
    let rgb := "#" ++ hexByte false r ++ hexByte false g ++ hexByte false b
    if a == 255 then rgb else rgb ++ hexByte false a

/--
Renders a color for TeX as six uppercase hex digits {lit}`RRGGBB`, suitable for xcolor's
{lit}`\definecolor{…}{HTML}{…}`. The alpha channel is dropped, since {lit}`xcolor`'s {lit}`HTML`
model is opaque RGB.
-/
public def tex : Color → String
  | .rgba r g b _ => hexByte true r ++ hexByte true g ++ hexByte true b

end Color

private def hexValue (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/--
Parses the hex digits of a color (no leading `#`) into RGBA byte channels. Accepts 3 digits
({lit}`rgb`, each digit doubled, opaque), 6 digits ({lit}`rrggbb`, opaque), or 8 digits
({lit}`rrggbbaa`).
-/
public def fromHexString (hex : String) : Except String (UInt8 × UInt8 × UInt8 × UInt8) := do
  let digit (c : Char) : Except String Nat :=
    match hexValue c with
    | some v => pure v
    | none => throw s!"'{c}' is not a hex digit"
  let byte (hi lo : Char) : Except String UInt8 := do
    return UInt8.ofNat ((← digit hi) * 16 + (← digit lo))
  match hex.toList with
  | [r, g, b] =>
    -- Each digit is doubled: `c` becomes `0xcc`, i.e. `c * 17`.
    return (UInt8.ofNat ((← digit r) * 17), UInt8.ofNat ((← digit g) * 17),
            UInt8.ofNat ((← digit b) * 17), 255)
  | [r1, r2, g1, g2, b1, b2] =>
    return (← byte r1 r2, ← byte g1 g2, ← byte b1 b2, 255)
  | [r1, r2, g1, g2, b1, b2, a1, a2] =>
    return (← byte r1 r2, ← byte g1 g2, ← byte b1 b2, ← byte a1 a2)
  | ds => throw s!"expected 3, 6, or 8 hex digits, got {ds.length}"
