/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Verso.Theme.Code

set_option linter.missingDocs true
set_option doc.verso true

/-!
The built-in {Lean.Doc.name}`Verso.Theme.CodeTheme` values. The default theme reproduces today's
hardcoded look so existing manuals render unchanged when no override is configured.
-/

namespace Verso.Theme

/--
The default code theme: typography-only styling that reproduces today's hardcoded look. Named
after the most ancient writing medium in use; other built-in themes live alongside it in the
{Lean.Doc.name}`Verso.Theme.CodeTheme` namespace.
-/
@[code_theme]
public def CodeTheme.ink : CodeTheme where
  name := "Ink"
  appearance := .light
