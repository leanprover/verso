/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import VersoManual.Theme
public import VersoManual.LicenseInfo.Licenses
public import Verso.Theme.Code.Defaults
public import Verso.Theme.Color.Palettes

set_option linter.missingDocs true
set_option doc.verso true

/-!
{open Verso.Theme}

Built-in {name}`ManualTheme` values. The default theme reproduces today's
chrome so existing manuals render unchanged when no override is configured. The dark counterpart
inverts the page and code backgrounds while preserving the typography-only token rendering.

Additional families ({lit}`Chromatic`, {lit}`Beacon`, etc.) ship colorful syntax palettes for
authors who want them; each family registers a light and a dark variant.
-/

namespace Verso.Theme

/-! # Defaults: Ink (light) and Argent (dark) -/

/--
The light default manual theme. Named after the most ancient writing medium in use, after the
inks made from soot or oak gall that have carried text for two thousand years. Typography and
chrome reproduce today's hardcoded look.

Other built-in themes live alongside it in the {name}`ManualTheme` namespace.
-/
@[manual_theme]
public def ManualTheme.ink : ManualTheme where
  toCodeTheme := CodeTheme.ink

/--
A common dark-appearance code-theme base: deep-charcoal backgrounds, brightened text, accent
colors chosen for readability against the dark substrate. Other dark themes extend this. Every
cascading field is overridden explicitly because Lean evaluates the {name}`CodeTheme`
defaults at construction time, so {lit}`CodeTheme.ink with textColor := …` would otherwise
leave dependent fields (token colors, message text colors, hover text) frozen at their
original-light values.
-/
private def darkCodeBase : CodeTheme :=
  let bg := color%#16181c
  let codeBg := color%#1e2026
  let text := color%#e8e8e8
{
  CodeTheme.ink with
  appearance := .dark,
  background := bg,
  codeBlockBackground := codeBg,
  textColor := text,
  codeColor := text,
  structureColor := text,
  -- Message text colors must read on the dark page background.
  errorColor := color%#ff8b8b,
  warningColor := text,
  infoColor := text,
  -- Token colors default to the bright code color; colorful themes override these per token.
  const := { color := text, weight := .regular, style := .normal, face := .mono },
  keyword := { color := text, weight := .bold, style := .normal, face := .mono },
  «var» := { color := text, weight := .regular, style := .italic, face := .mono },
  -- Hover popups read text on a slightly lighter surface.
  hoverBackground := color%#2a2d33,
  hoverText := text,
  hoverBorderColor := color%#aaaaaa,
  hoverSeparatorColor := color%#3a3d44,
  tokenHighlightBackground := color%#33363d,
  -- Tactic-state background inherits from `codeBlockBackground`; only the border needs a
  -- lighter color to read on the dark substrate.
  tacticStateBorderColor := color%#aaaaaa,
  selectedColor := color%#2a3f55,
  -- Highlight accents on a dark substrate: a saturated tone that the bright text still reads on.
  highlightOnCode := color%#3a2f00,
  highlightOnText := color%#3a2f00,
  uiOnCode := color%#aaaaaa
}

/--
A common dark-appearance chrome base reused by the shipped dark themes. The chrome variables
inherit from the dark code base where possible (so a uniform dark look) and use explicit values
where contrast requires lighter chrome accents (borders, muted text, links). The burger menu
lines pick up the text color (so the lines themselves are visible against the page background;
without this override they default to the light theme's near-black {lit}`#0e2431`, which is
invisible on a dark substrate and shows only the surrounding {lit}`drop-shadow`).
-/
private def darkChromeFields (code : CodeTheme) : ManualTheme := {
  toCodeTheme := code,
  surfaceColor := color%#1f2229,
  tocBackground := color%#1a1c22,
  borderColor := color%#a0a3ab,
  mutedColor := color%#a8acb5,
  linkColor := color%#6cb6ff,
  visitedLinkColor := color%#a98aff,
  burgerHiddenColor := code.textColor,
  burgerVisibleColor := code.textColor,
  burgerHiddenShadowColor := code.background,
  burgerVisibleShadowColor := code.background
}

/--
The dark default manual theme. Named after silver, the ink of choice for the dark-substrate
manuscript traditions: silver-on-purple Byzantine and Carolingian codices like the *Codex
Argenteus*, Flemish "Black Hours" such as Morgan MS M.493, and Korean *eunja sagyeong* (은자사경)
sutras transcribed in silver ink on indigo *kamji* paper during the Goryeo dynasty. Same
typography-only token rendering as {name}`ManualTheme.ink`, with inverted
backgrounds and a light text color.
-/
@[manual_theme]
public def ManualTheme.argent : ManualTheme :=
  darkChromeFields { darkCodeBase with name := "Argent" }

/-! # Chromatic — colorful syntax accents -/

/--
Chromatic light: full color plus typography for syntax tokens on a light background. Palette
chosen so each token color meets WCAG AA on white and remains visually distinct under all three
dichromacies (variables use a dark slate so the bold/italic typography is the dominant signal).
-/
@[manual_theme]
public def ManualTheme.chromaticLight : ManualTheme where
  toCodeTheme := {
    CodeTheme.ink with
    name := "Chromatic Light",
    keyword.color := color%#a02828,
    const.color := color%#0b6b4f,
    «var».color := color%#404040
  }

/-- Chromatic dark: the colored Lean palette on a deep-charcoal background. -/
@[manual_theme]
public def ManualTheme.chromaticDark : ManualTheme :=
  darkChromeFields {
    darkCodeBase with
    name := "Chromatic Dark",
    keyword.color := color%#ff8b8b,
    const.color := color%#6cb6ff,
    «var».color := color%#c4c4c4
  }

/-! # Beacon — colorblind-safe syntax accents (Okabe-Ito) -/

/--
Beacon light: a colorblind-safe syntax palette drawn from the Okabe-Ito set. Black on white
chrome; tokens use Okabe-Ito blue/orange/bluish-green so they stay distinguishable under all
three dichromacies.
-/
@[manual_theme]
public def ManualTheme.beaconLight : ManualTheme where
  toCodeTheme := {
    CodeTheme.ink with
    name := "Beacon Light",
    sourceLink := some Color.Palettes.OkabeIto.sourceLink,
    keyword.color := color%#005b8c,
    const.color := color%#5b3500,
    «var».color := color%#9c2400
  }

/--
Beacon dark: the Okabe-Ito palette on a near-black background, with brightened variants chosen
to keep distance under each dichromacy on the darker substrate.
-/
@[manual_theme]
public def ManualTheme.beaconDark : ManualTheme :=
  darkChromeFields {
    darkCodeBase with
    name := "Beacon Dark",
    sourceLink := some Color.Palettes.OkabeIto.sourceLink,
    keyword.color := Color.Palettes.OkabeIto.skyBlue,
    const.color := color%#5bd6a4,
    «var».color := color%#f5a85a
  }

/-! # Solarized — Ethan Schoonover's standard palette -/

open Color.Palettes.Solarized in
/--
Solarized light: Schoonover's standard cream-on-paper palette
({lit}`base3` background, {lit}`base01` primary content). Token accents reuse the named hues
from the upstream Solarized definition.
-/
@[manual_theme]
public def ManualTheme.solarizedLight : ManualTheme :=
  {
    toCodeTheme := {
      CodeTheme.ink with
      name := s!"{Color.Palettes.Solarized.name} Light",
      sourceLink := some Color.Palettes.Solarized.sourceLink,
      background := base3,
      codeBlockBackground := base2,
      textColor := base01,
      codeColor := base01,
      structureColor := base01,
      warningColor := base01,
      infoColor := base01,
      errorColor := red,
      errorIndicatorColor := red,
      warningIndicatorColor := yellow,
      infoIndicatorColor := blue,
      hoverBackground := base2,
      hoverText := base01,
      hoverBorderColor := base1,
      hoverSeparatorColor := base1,
      tokenHighlightBackground := base2,
      tacticStateBorderColor := base1,
      selectedColor := base2,
      highlightOnCode := color%#f7e7a3,
      uiOnCode := base1,
      keyword.color := green,
      const.color := blue,
      «var».color := violet
    },
    surfaceColor := base2,
    tocBackground := base2,
    borderColor := base01,
    mutedColor := base00,
    linkColor := blue,
    visitedLinkColor := violet,
    licenses := #[Verso.Genre.Manual.Licenses.solarized]
  }

open Color.Palettes.Solarized in
/--
Solarized dark: Schoonover's standard {lit}`base03` background with body text on {lit}`base1`.
Token accents are brightened off the standard palette so they keep clear contrast on the dark
substrate.
-/
@[manual_theme]
public def ManualTheme.solarizedDark : ManualTheme :=
  { darkChromeFields {
    darkCodeBase with
    name := s!"{Color.Palettes.Solarized.name} Dark",
    sourceLink := some Color.Palettes.Solarized.sourceLink,
    background := base03,
    codeBlockBackground := base02,
    textColor := base1,
    codeColor := base1,
    structureColor := base1,
    warningColor := base1,
    infoColor := base1,
    errorColor := color%#ff8b8b,
    errorIndicatorColor := red,
    warningIndicatorColor := yellow,
    infoIndicatorColor := blue,
    hoverBackground := base02,
    hoverText := base1,
    hoverBorderColor := base01,
    hoverSeparatorColor := base01,
    tokenHighlightBackground := base02,
    tacticStateBorderColor := base01,
    selectedColor := base02,
    highlightOnCode := color%#3a2f00,
    uiOnCode := base1,
    keyword.color := color%#b3d100,
    const.color := color%#6cb6ff,
    «var».color := color%#a98aff
  } with
    -- Override the dark-chrome link defaults with the canonical Solarized blue/violet (they
    -- clear contrast on `base03`).
    linkColor := blue,
    visitedLinkColor := violet,
    licenses := #[Verso.Genre.Manual.Licenses.solarized] }

/-! # Sandstone — warm sepia -/

/-- Sandstone light: a warm cream background with terracotta and umber accents. -/
@[manual_theme]
public def ManualTheme.sandstoneLight : ManualTheme where
  toCodeTheme := {
    CodeTheme.ink with
    name := "Sandstone Light",
    background := color%#faf5ee,
    codeBlockBackground := color%#f3e9d6,
    textColor := color%#3b2a17,
    codeColor := color%#3b2a17,
    structureColor := color%#3b2a17,
    warningColor := color%#3b2a17,
    infoColor := color%#3b2a17,
    errorColor := color%#a83232,
    errorIndicatorColor := color%#c0392b,
    warningIndicatorColor := color%#a05a00,
    infoIndicatorColor := color%#1f6f8b,
    hoverBackground := color%#f3e9d6,
    hoverText := color%#3b2a17,
    hoverBorderColor := color%#8c7257,
    hoverSeparatorColor := color%#8c7257,
    tokenHighlightBackground := color%#f3e9d6,
    tacticStateBackground := color%#f3e9d6,
    tacticStateBorderColor := color%#8c7257,
    selectedColor := color%#f4d5a8,
    highlightOnCode := color%#f4d5a8,
    uiOnCode := color%#8c7257,
    keyword.color := color%#a04a00,
    const.color := color%#1f6f8b,
    «var».color := color%#3b2a17
  }
  surfaceColor := color%#f3e9d6
  tocBackground := color%#f3e9d6
  borderColor := color%#8c7257
  mutedColor := color%#7a5a40
  linkColor := color%#a04a00
  visitedLinkColor := color%#7a3a91

/--
Sandstone dark: weathered canyon walls at dusk — deep terracotta substrate with sunlit-buff
text and warm vermilion / honey accents. No cool blues: the previous version's {lit}`#80c8e8`
const broke the warm-palette family. Inspired by the Sedona red rocks, Petra at twilight, and
the Vermilion Cliffs of Arizona-Utah.
-/
@[manual_theme]
public def ManualTheme.sandstoneDark : ManualTheme :=
  let base := darkChromeFields {
    darkCodeBase with
    name := "Sandstone Dark",
    -- Dark canyon-shadow substrate. Slightly warmer than the legacy `#241a10`, with more
    -- red and less yellow so it reads as weathered stone rather than coffee.
    background := color%#2d1810,
    codeBlockBackground := color%#3a2118,
    -- Sunlit-buff text — the colour a sandstone face takes in late-afternoon light.
    textColor := color%#f3d5a3,
    codeColor := color%#f3d5a3,
    structureColor := color%#f3d5a3,
    warningColor := color%#f3d5a3,
    infoColor := color%#f3d5a3,
    errorColor := color%#ff8b8b,
    errorIndicatorColor := color%#ff6f6f,
    warningIndicatorColor := color%#e0a060,
    infoIndicatorColor := color%#ffae5a,
    hoverBackground := color%#4a2c20,
    hoverText := color%#f3d5a3,
    hoverBorderColor := color%#a87c52,
    hoverSeparatorColor := color%#5e3925,
    tokenHighlightBackground := color%#4a2c20,
    tacticStateBackground := color%#3a2118,
    tacticStateBorderColor := color%#a87c52,
    selectedColor := color%#553626,
    highlightOnCode := color%#6b4500,
    highlightOnText := color%#6b4500,
    uiOnCode := color%#a87c52,
    -- Vermilion keyword, honey const, cream var (italic). All three are warm, distinguished
    -- by hue *and* lightness so the palette stays distinct under most dichromacies even
    -- without a cool accent.
    keyword.color := color%#ff8c4a,
    const.color := color%#ffc266,
    «var».color := color%#f3d5a3
  }
  -- Override the generic dark-chrome accents with sandstone-tuned values so the search box
  -- border, ToC background, and link colours stay in the warm family.
  { base with
    surfaceColor := color%#3a2118,
    tocBackground := color%#2d1810,
    borderColor := color%#a87c52,
    mutedColor := color%#c89866,
    linkColor := color%#ffae5a,
    visitedLinkColor := color%#d49a8a }

/-! # Steel (light) and Slate (dark) — cool high-contrast (Coal/Navy inspired) -/

/-- Slate light: cool, near-white substrate with deep navy text. -/
@[manual_theme]
public def ManualTheme.steel : ManualTheme where
  toCodeTheme := {
    CodeTheme.ink with
    name := "Steel",
    background := color%#f4f6f8,
    codeBlockBackground := color%#e3e8ee,
    textColor := color%#0e2431,
    codeColor := color%#0e2431,
    structureColor := color%#0e2431,
    warningColor := color%#0e2431,
    infoColor := color%#0e2431,
    errorColor := color%#a92020,
    errorIndicatorColor := color%#c0392b,
    warningIndicatorColor := color%#9c6500,
    infoIndicatorColor := color%#1a5ea8,
    hoverBackground := color%#e3e8ee,
    hoverText := color%#0e2431,
    hoverBorderColor := color%#46566a,
    hoverSeparatorColor := color%#46566a,
    tokenHighlightBackground := color%#e3e8ee,
    tacticStateBackground := color%#e3e8ee,
    tacticStateBorderColor := color%#46566a,
    selectedColor := color%#c5d4e3,
    highlightOnCode := color%#fff3b0,
    uiOnCode := color%#46566a,
    keyword.color := color%#1a5ea8,
    const.color := color%#2a6f4f,
    «var».color := color%#0e2431
  }
  surfaceColor := color%#e3e8ee
  tocBackground := color%#e3e8ee
  borderColor := color%#46566a
  mutedColor := color%#465a70
  linkColor := color%#1a5ea8
  visitedLinkColor := color%#6c4ea8

/-- Slate dark: coal/navy substrate, brightened slate accents. -/
@[manual_theme]
public def ManualTheme.slate : ManualTheme :=
  darkChromeFields {
    darkCodeBase with
    name := "Slate",
    background := color%#0e1822,
    codeBlockBackground := color%#172533,
    textColor := color%#dfe6ee,
    codeColor := color%#dfe6ee,
    structureColor := color%#dfe6ee,
    warningColor := color%#dfe6ee,
    infoColor := color%#dfe6ee,
    errorColor := color%#ff8b8b,
    errorIndicatorColor := color%#ff6f6f,
    warningIndicatorColor := color%#e6b04a,
    infoIndicatorColor := color%#6cb6ff,
    hoverBackground := color%#1f3142,
    hoverText := color%#dfe6ee,
    hoverBorderColor := color%#7a8aa0,
    hoverSeparatorColor := color%#3a4a5e,
    tokenHighlightBackground := color%#1f3142,
    tacticStateBackground := color%#172533,
    tacticStateBorderColor := color%#7a8aa0,
    selectedColor := color%#284a6a,
    highlightOnCode := color%#3a2f00,
    uiOnCode := color%#7a8aa0,
    keyword.color := color%#6cb6ff,
    const.color := color%#7ad9a0,
    «var».color := color%#dfe6ee
  }

/-! # Hearth — cottagecore (cream/sage light, candlelit deep-olive dark) -/

/--
Hearth light: a cream substrate with sage and dusty rose accents and a serifed structure font.
-/
@[manual_theme]
public def ManualTheme.hearthLight : ManualTheme where
  toCodeTheme := {
    CodeTheme.ink with
    name := "Hearth Light",
    background := color%#f7f1e3,
    codeBlockBackground := color%#ede4cf,
    textColor := color%#3d2f1f,
    codeColor := color%#3d2f1f,
    structureColor := color%#3d2f1f,
    warningColor := color%#3d2f1f,
    infoColor := color%#3d2f1f,
    errorColor := color%#a04050,
    errorIndicatorColor := color%#a04050,
    warningIndicatorColor := color%#a07020,
    infoIndicatorColor := color%#2f6e58,
    hoverBackground := color%#ede4cf,
    hoverText := color%#3d2f1f,
    hoverBorderColor := color%#7a6952,
    hoverSeparatorColor := color%#7a6952,
    tokenHighlightBackground := color%#ede4cf,
    tacticStateBackground := color%#ede4cf,
    tacticStateBorderColor := color%#7a6952,
    selectedColor := color%#e3cfae,
    highlightOnCode := color%#e3cfae,
    uiOnCode := color%#7a6952,
    keyword.color := color%#2f6e58,
    const.color := color%#a04050,
    «var».color := color%#3d2f1f
  }
  textFace := .serif
  structureFace := .serif
  surfaceColor := color%#ede4cf
  tocBackground := color%#ede4cf
  borderColor := color%#7a6952
  mutedColor := color%#6b5640
  linkColor := color%#2f6e58
  visitedLinkColor := color%#7a3a91

/--
Hearth dark: a deep-olive candlelit substrate with warm cream text. Serifed structure font, same
muted sage and dusty rose accents as the light variant.
-/
@[manual_theme]
public def ManualTheme.hearthDark : ManualTheme :=
  let base := darkChromeFields {
    darkCodeBase with
    name := "Hearth Dark",
    background := color%#1e1e14,
    codeBlockBackground := color%#262619,
    textColor := color%#f1e7d2,
    codeColor := color%#f1e7d2,
    structureColor := color%#f1e7d2,
    warningColor := color%#f1e7d2,
    infoColor := color%#f1e7d2,
    errorColor := color%#ff8b8b,
    errorIndicatorColor := color%#ff7a90,
    warningIndicatorColor := color%#e6a85a,
    infoIndicatorColor := color%#80c8a8,
    hoverBackground := color%#33321f,
    hoverText := color%#f1e7d2,
    hoverBorderColor := color%#a08a64,
    hoverSeparatorColor := color%#4a4628,
    tokenHighlightBackground := color%#33321f,
    tacticStateBackground := color%#262619,
    tacticStateBorderColor := color%#a08a64,
    selectedColor := color%#33321f,
    highlightOnCode := color%#5c4a00,
    uiOnCode := color%#a08a64,
    keyword.color := color%#9adcb0,
    const.color := color%#f5a8b8,
    «var».color := color%#f1e7d2
  }
  { base with textFace := .serif, structureFace := .serif }
