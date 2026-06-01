/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Verso.Theme.Color.Palettes.Solarized
public import Verso.Theme.Color.Palettes.OkabeIto

/-!
{open Verso.Theme}

Named reference palettes used by the shipped themes. Each palette module exposes:

- a {lit}`name : String` and {lit}`sourceLink : SourceLink` for the picker to display
  alongside themes that build on the palette;
- a set of named {name}`Color` constants holding the canonical hex values.
-/
