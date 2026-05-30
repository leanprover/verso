/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import VersoManual.Theme
public import Verso.Theme.Code.Defaults

set_option linter.missingDocs true
set_option doc.verso true

/-!
Built-in {Lean.Doc.name}`Verso.Theme.ManualTheme` values. The default theme reproduces today's
chrome so existing manuals render unchanged when no override is configured.
-/

namespace Verso.Theme

/--
The default manual theme: typography and chrome that reproduce today's hardcoded look. Other
built-in themes live alongside it in the {Lean.Doc.name}`Verso.Theme.ManualTheme` namespace.
-/
@[manual_theme]
public def ManualTheme.Default : ManualTheme where
  toCodeTheme := CodeTheme.Default
