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
{open Verso.Theme}

The built-in {Lean.Doc.name}`CodeTheme` values. The default theme reproduces today's hardcoded look
so existing manuals render unchanged when no override is configured.
-/

namespace Verso.Theme

/--
The default code theme.

This theme uses only typographical features to distinguish code elements, rather than color.
The page is white, body and code text are black, and diagnostic accents match the pre-theming
hardcoded values.
-/
@[code_theme]
public def CodeTheme.ink : CodeTheme where
  name := "Ink"
  appearance := .light
  background := Color.white
  textColor := Color.black
  selectedColor := color%#ddeeff
  infoIndicatorColor := color%#4777ff
  warningIndicatorColor := color%#d97706
  errorColor := color%#cc0000
  errorIndicatorColor := color%#ff0000
  hoverBackground := color%#e5e5e5
  hoverBorderColor := Color.black
  hoverSeparatorColor := color%#cccccc
  tokenHighlightBackground := color%#eeeeee
  tacticStateBorderColor := color%#888888
  highlightOnCode := color%#fff3b0
  uiOnCode := color%#888888
