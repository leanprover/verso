/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The Nord hex constants below are reproduced from the *Nord* palette by Sven Greb (Arctic Ice
Studio), distributed under the MIT license. The notice is reproduced here verbatim per the
license's attribution clause; the manual genre also includes it in the attribution page of any
generated manual that includes a Nord theme.

  MIT License (MIT)

  Copyright (c) 2016-present Sven Greb <development@svengreb.de> (https://www.svengreb.de)

  Permission is hereby granted, free of charge, to any person obtaining a copy of this software
  and associated documentation files (the "Software"), to deal in the Software without
  restriction, including without limitation the rights to use, copy, modify, merge, publish,
  distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the
  Software is furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all copies or
  substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
  BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
  DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-/
module

public import Verso.Theme.Color.Basic
public import Verso.Theme.Color.Syntax
public import Verso.Theme.SourceLink

set_option linter.missingDocs true
set_option doc.verso true

/-!
{open Verso.Theme}

Sven Greb's _Nord_ palette as named {name}`Color` constants. Sixteen colors organized in four
groups, taken from the [canonical reference](https://www.nordtheme.com/docs/colors-and-palettes):

: Polar Night

  ({lit}`nord0`–{lit}`nord3`): deep arctic-night base, used for dark-substrate backgrounds and code
  surfaces. : Snow Storm

  ({lit}`nord4`–{lit}`nord6`): light, frosty whites for body text on dark backgrounds (and
  substrates on light variants).

: Frost

  ({lit}`nord7`–{lit}`nord10`): four blue-green hues, the canonical syntax accents.

: Aurora

  ({lit}`nord11`–{lit}`nord15`): warm accent hues (red, orange, yellow, green, purple) used for
  diagnostics and additional syntax categories.
-/

namespace Verso.Theme.Color.Palettes.Nord

/-! # Identity -/

/-- The palette's display name, suitable as a prefix when naming themes built on it. -/
public def name : String := "Nord"

/-- The canonical Nord homepage, shown in the picker for themes that use this palette. -/
public def sourceLink : SourceLink :=
  { url := "https://www.nordtheme.com/", text := "nordtheme.com" }

/-! # Polar Night -/

/--
{lit}`nord0` — Polar Night, origin color. The canonical Nord background on dark-ambiance
substrates; also serves as the plain-text color on bright-ambiance (light) backgrounds.
-/
public def nord0 : Color := color%#2e3440
/--
{lit}`nord1` — Polar Night, a shade lighter. Used for elevated UI surfaces such as status
bars, panels, and buttons over the {lit}`nord0` substrate.
-/
public def nord1 : Color := color%#3b4252
/--
{lit}`nord2` — Polar Night, mid shade. Used for active editor lines and selection
highlighting against the {lit}`nord0` substrate.
-/
public def nord2 : Color := color%#434c5e
/--
{lit}`nord3` — Polar Night, the lightest shade. Used for comments, indent guides, and other
subtle UI accents.
-/
public def nord3 : Color := color%#4c566a

/-! # Snow Storm -/

/--
{lit}`nord4` — Snow Storm, the darkest of the light shades. Used for the editor caret on dark
substrates and for syntax variables and constants.
-/
public def nord4 : Color := color%#d8dee9
/--
{lit}`nord5` — Snow Storm, mid. Used for subtle UI text and for selection highlighting on
bright-ambiance backgrounds.
-/
public def nord5 : Color := color%#e5e9f0
/--
{lit}`nord6` — Snow Storm, the lightest shade. The canonical bright-ambiance background; also
serves as the plain syntax-text color on dark backgrounds.
-/
public def nord6 : Color := color%#eceff4

/-! # Frost -/

/--
{lit}`nord7` — Frost, a calm muted cyan-green. Documented role: classes, types, and
primitives in syntax highlighting.
-/
public def nord7 : Color := color%#8fbcbb
/--
{lit}`nord8` — Frost, brighter cyan; Nord's primary syntax accent. Documented role:
declarations, calls, and execution statements.
-/
public def nord8 : Color := color%#88c0d0
/--
{lit}`nord9` — Frost, blue. Nord's secondary syntax accent. Documented role: keywords as
well as support characters, operators, and tags.
-/
public def nord9 : Color := color%#81a1c1
/--
{lit}`nord10` — Frost, deep blue. Nord's tertiary syntax accent. Documented role: pragmas
and preprocessor statements (e.g. the {lit}`#include` directive in C).
-/
public def nord10 : Color := color%#5e81ac

/-! # Aurora -/

/--
{lit}`nord11` — Aurora red. Documented role: error states, Git deletions in UI chrome, and
detected syntax errors.
-/
public def nord11 : Color := color%#bf616a
/--
{lit}`nord12` — Aurora orange. Documented role: indicators for "advanced functionality";
annotations and decorators in syntax highlighting.
-/
public def nord12 : Color := color%#d08770
/--
{lit}`nord13` — Aurora yellow. Documented role: warning states, modified items in UI chrome,
and escape characters in strings.
-/
public def nord13 : Color := color%#ebcb8b
/--
{lit}`nord14` — Aurora green. Documented role: success states, Git additions, and string
literals in syntax highlighting.
-/
public def nord14 : Color := color%#a3be8c
/--
{lit}`nord15` — Aurora purple. Documented role: highlighting "uncommon functionality";
numeric and floating-point literals in syntax highlighting.
-/
public def nord15 : Color := color%#b48ead
