/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso
import VersoManual
import ThemeTestDoc

open Verso Verso.Theme
open Verso.Genre Manual

/-!
The customized {Lean.Doc.name}`Verso.Theme.CodeTheme` used by the browser test. Each color field
holds a distinct sentinel hex value so Playwright can identify which theme field a rendered DOM
color comes from.
-/
def testTheme : CodeTheme := {
  name := "ThemeTest",
  appearance := .light,
  background := color%#000101,
  codeBlockBackground := color%#000202,
  textColor := color%#000303,
  codeColor := color%#000404,
  structureColor := color%#000505,
  selectedColor := color%#000606,
  infoColor := color%#000707,
  infoIndicatorColor := color%#000808,
  warningColor := color%#000909,
  warningIndicatorColor := color%#000a0a,
  errorColor := color%#000b0b,
  errorIndicatorColor := color%#000c0c,
  hoverBackground := color%#000d0d,
  hoverBorderColor := color%#000e0e,
  hoverText := color%#000f0f,
  hoverSeparatorColor := color%#001010,
  tokenHighlightBackground := color%#001111,
  tacticStateBackground := color%#001212,
  tacticStateBorderColor := color%#001313,
  highlightOnCode := color%#001414,
  highlightOnText := color%#001515,
  uiOnCode := color%#001616,
  const := { color := color%#001717, weight := 500, style := .italic, face := .sans },
  keyword := { color := color%#001818, weight := 800, style := .italic, face := .serif },
  «var» := { color := color%#001919, weight := 300, style := .normal, face := .mono },
}

def config : Config where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1

def main : List String → IO UInt32 :=
  manualMain (%doc ThemeTestDoc)
    (config := { config with codeTheme := testTheme })
