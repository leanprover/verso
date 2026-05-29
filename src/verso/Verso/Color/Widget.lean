/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public meta import Lean.Widget.UserWidget
public meta import Verso.Color.Basic
public meta import Verso.Color.Math

set_option linter.missingDocs true
set_option doc.verso true

/-!
The InfoView preview widget for colors. The CSS form is computed in Lean and handed to the widget,
so the JavaScript only has to draw the swatch.
-/

namespace Verso

public section

open Lean Widget

/-- A read-only InfoView swatch that previews a color. -/
@[widget_module]
meta def colorWidget : Lean.Widget.Module where
  javascript := include_str "color-swatch.js"

/--
Attaches the color-preview widget to {name}`stx`. The widget shows {name}`color` together with how
it appears under each of the three dichromacies, all rendered to CSS in Lean.
-/
meta def saveColorWidget (color : Color) (stx : Syntax) : CoreM Unit :=
  let props := Json.mkObj [
    ("css", .str color.css),
    ("protanopia", .str (Color.dichromacy .protanopia color).css),
    ("deuteranopia", .str (Color.dichromacy .deuteranopia color).css),
    ("tritanopia", .str (Color.dichromacy .tritanopia color).css)]
  savePanelWidgetInfo colorWidget.javascriptHash (pure props) stx
