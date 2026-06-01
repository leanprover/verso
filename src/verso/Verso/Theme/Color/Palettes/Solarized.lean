/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The Solarized hex constants below are reproduced from Ethan Schoonover's Solarized palette,
distributed under the MIT license. The notice is reproduced here verbatim per the license's
attribution clause; the manual genre also includes it in the attribution page of any generated
manual that includes a Solarized theme.

  Copyright (c) 2011 Ethan Schoonover

  Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
  associated documentation files (the "Software"), to deal in the Software without restriction,
  including without limitation the rights to use, copy, modify, merge, publish, distribute,
  sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all copies or
  substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
  NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
  DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
  OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-/
module

public import Verso.Theme.Color.Basic
public import Verso.Theme.Color.Syntax
public import Verso.Theme.SourceLink

set_option linter.missingDocs true
set_option doc.verso true

/-!
{open Verso.Theme}

Ethan Schoonover's _Solarized_ palette as named {name}`Color` constants. Sixteen
colors: eight monotone shades (the {lit}`base*` ramp) plus eight accent hues. The hex values are
the canonical ones from the [upstream reference](https://ethanschoonover.com/solarized/).

The ramp's design rule is that any {lit}`base0X` (with leading zero) is dark-mode body text and
any {lit}`baseY` is light-mode body text; the rest progress symmetrically between background and
foreground for each appearance.
-/

namespace Verso.Theme.Color.Palettes.Solarized

/-! # Identity -/

/-- The palette's display name, suitable as a prefix when naming themes built on it. -/
public def name : String := "Solarized"

/-- The canonical Solarized homepage, shown in the picker for themes that use this palette. -/
public def sourceLink : SourceLink where
  url := "https://ethanschoonover.com/solarized/"
  text := "ethanschoonover.com/solarized"

/-! # Monotone ramp -/

/-- {lit}`base03` — Solarized dark background. -/
public def base03 : Color := color%#002b36
/-- {lit}`base02` — Solarized dark highlights / content background. -/
public def base02 : Color := color%#073642
/-- {lit}`base01` — Solarized comments / secondary content (dark). Light primary content. -/
public def base01 : Color := color%#586e75
/-- {lit}`base00` — Solarized light secondary content. -/
public def base00 : Color := color%#657b83
/-- {lit}`base0` — Solarized dark body text. -/
public def base0 : Color := color%#839496
/-- {lit}`base1` — Solarized dark comments / secondary content. -/
public def base1 : Color := color%#93a1a1
/-- {lit}`base2` — Solarized light highlights / content background. -/
public def base2 : Color := color%#eee8d5
/-- {lit}`base3` — Solarized light background. -/
public def base3 : Color := color%#fdf6e3

/-! # Accent hues -/

/-- Solarized yellow. -/
public def yellow : Color := color%#b58900
/-- Solarized orange. -/
public def orange : Color := color%#cb4b16
/-- Solarized red. -/
public def red : Color := color%#dc322f
/-- Solarized magenta. -/
public def magenta : Color := color%#d33682
/-- Solarized violet. -/
public def violet : Color := color%#6c71c4
/-- Solarized blue. -/
public def blue : Color := color%#268bd2
/-- Solarized cyan. -/
public def cyan : Color := color%#2aa198
/-- Solarized green. -/
public def green : Color := color%#859900

end Verso.Theme.Color.Palettes.Solarized
