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

@[manual_theme]
def testManualTheme : ManualTheme := {
  ManualTheme.ink with
  toCodeTheme := testTheme,
  surfaceColor := color%#001a1a,
  headerBackground := color%#001b1b,
  tocBackground := color%#001c1c,
  borderColor := color%#001d1d,
  mutedColor := color%#001e1e,
  highlightColor := color%#001f1f,
  linkColor := color%#002020,
  visitedLinkColor := color%#002121,
  tocTextColor := color%#002222,
  burgerVisibleColor := color%#002323,
  burgerVisibleShadowColor := color%#002424,
  burgerHiddenColor := color%#002525,
  burgerHiddenShadowColor := color%#002626
}

/--
Dark counterpart to `testManualTheme`. The validation pass requires a registered dark theme
for `defaultDarkTheme`, but the test only inspects the unscoped `:root` block (the
single-mode default, here `.light`), so the same sentinel palette under `.dark` is fine.
-/
@[manual_theme]
def testManualThemeDark : ManualTheme := {
  testManualTheme with
  toCodeTheme := { testTheme with name := "ThemeTest Dark", appearance := .dark }
}

def main : List String → IO UInt32 :=
  manualMain (%doc ThemeTestDoc)
    (config := { config with
      defaultLightTheme := ``testManualTheme,
      defaultDarkTheme := ``testManualThemeDark,
      -- The sentinel palette deliberately violates accessibility; the test exercises rendering,
      -- not the accessibility checks.
      strictThemeCoverage := false,
      strictDefaultThemeAccessibility := false,
      warnPerThemeAccessibility := false })
