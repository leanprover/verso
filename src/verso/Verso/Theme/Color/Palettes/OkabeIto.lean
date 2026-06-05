/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Verso.Theme.Color.Basic
public import Verso.Theme.Color.Syntax
public import Verso.Theme.SourceLink

set_option linter.missingDocs true
set_option doc.verso true

/-!
{open Verso.Theme}

[Masataka Okabe and Kei Ito's colorblind-safe palette (2002)](https://jfly.uni-koeln.de/color/) as
named {name}`Color` constants. The eight hues stay distinguishable under protanopia, deuteranopia,
and tritanopia, so they are a standard reference set for data visualization and code highlighting
that must remain readable to dichromat readers.
-/

namespace Verso.Theme.Color.Palettes.OkabeIto

/-! # Identity -/

/-- The palette's display name, suitable as a prefix when naming themes built on it. -/
public def name : String := "Okabe-Ito"

/-- The canonical Okabe-Ito reference page, shown in the picker for themes that use it. -/
public def sourceLink : SourceLink :=
  { url := "https://jfly.uni-koeln.de/color/", text := "jfly.uni-koeln.de/color" }

/-! # Hues -/

/-- Okabe-Ito black: {lit}`#000000`. -/
public def black : Color := color%#000000
/-- Okabe-Ito orange: {lit}`#e69f00`. -/
public def orange : Color := color%#e69f00
/-- Okabe-Ito sky blue: {lit}`#56b4e9`. -/
public def skyBlue : Color := color%#56b4e9
/-- Okabe-Ito bluish green: {lit}`#009e73`. -/
public def bluishGreen : Color := color%#009e73
/-- Okabe-Ito yellow: {lit}`#f0e442`. -/
public def yellow : Color := color%#f0e442
/-- Okabe-Ito blue: {lit}`#0072b2`. -/
public def blue : Color := color%#0072b2
/-- Okabe-Ito vermillion: {lit}`#d55e00`. -/
public def vermillion : Color := color%#d55e00
/-- Okabe-Ito reddish purple: {lit}`#cc79a7`. -/
public def reddishPurple : Color := color%#cc79a7

end Verso.Theme.Color.Palettes.OkabeIto
