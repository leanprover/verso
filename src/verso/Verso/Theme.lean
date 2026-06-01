/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Verso.Theme.Color
public import Verso.Theme.Code
public import Verso.Theme.Code.Defaults

/-!
The full theme API: typed colors, color math and accessibility checks, named reference
palettes, and the genre-neutral {lit}`CodeTheme` with its built-in defaults. Genres that
need theme support (the manual genre) re-export their own theme additions on top of this.
-/
