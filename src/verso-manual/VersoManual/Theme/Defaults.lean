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
  surfaceColor := color%#f8f9fa
  tocBackground := color%#fafafa
  borderColor := color%#878787
  mutedColor := color%#777777
  linkColor := color%#0066cc
  burgerVisibleShadowColor := Color.white
  burgerHiddenColor := color%#0e2431
  burgerHiddenShadowColor := Color.white

/--
A common dark-appearance code-theme base: deep-charcoal backgrounds, brightened text, accent
colors chosen for readability against the dark substrate. Other dark themes extend this.
Every field whose default references another field is overridden explicitly: Lean evaluates
defaults when the source theme is constructed, so {lit}`CodeTheme.ink with textColor := …`
would otherwise leave dependent fields (token colors, message text colors, hover text,
tactic-state background) frozen at their original light-substrate values.
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
  literal := { color := text, weight := .regular, style := .normal, face := .mono },
  literalString := { color := text, weight := .regular, style := .normal, face := .mono },
  docComment := { color := text, weight := .regular, style := .italic, face := .mono },
  sort := { color := text, weight := .regular, style := .normal, face := .mono },
  levelVar := { color := text, weight := .regular, style := .italic, face := .mono },
  levelConst := { color := text, weight := .regular, style := .normal, face := .mono },
  levelOp := { color := text, weight := .regular, style := .normal, face := .mono },
  moduleName := { color := text, weight := .regular, style := .normal, face := .mono },
  delim := { color := text, weight := .regular, style := .normal, face := .mono },
  operator := { color := text, weight := .regular, style := .normal, face := .mono },
  bracket := { color := text, weight := .regular, style := .normal, face := .mono },
  separator := { color := text, weight := .regular, style := .normal, face := .mono },
  literalNumber := { color := text, weight := .regular, style := .normal, face := .mono },
  literalChar := { color := text, weight := .regular, style := .normal, face := .mono },
  comment := { color := text, weight := .regular, style := .normal, face := .mono },
  commentDelim := { color := text, weight := .regular, style := .normal, face := .mono },
  -- Hover popups read text on a slightly lighter surface.
  hoverBackground := color%#2a2d33,
  hoverText := text,
  hoverBorderColor := color%#aaaaaa,
  hoverSeparatorColor := color%#3a3d44,
  tokenHighlightBackground := color%#33363d,
  -- Tactic state uses the same surface as code blocks. `tacticStateBackground`'s default
  -- is `codeBlockBackground`, but defaults are evaluated when the source theme is constructed
  -- — `CodeTheme.ink` froze it at white — and `with` updates don't re-evaluate them. The
  -- override has to be explicit here so the dark substrate flows through.
  tacticStateBackground := codeBg,
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
A light-appearance chrome base reused by the shipped light themes. Mirrors `darkChromeFields`
for themes that want the default light chrome (Ink-style surface, ToC, borders, link colors,
and burger lines) without spelling out each field. Themes with custom chrome set the fields
explicitly.
-/
private def lightChromeFields (code : CodeTheme) : ManualTheme := {
  toCodeTheme := code,
  surfaceColor := color%#f8f9fa,
  tocBackground := color%#fafafa,
  borderColor := color%#878787,
  mutedColor := color%#777777,
  linkColor := color%#0066cc,
  burgerVisibleShadowColor := Color.white,
  burgerHiddenColor := color%#0e2431,
  burgerHiddenShadowColor := Color.white
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
public def ManualTheme.chromaticLight : ManualTheme :=
  lightChromeFields {
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

open Color.Palettes.OkabeIto in
/--
Beacon light: a colorblind-safe syntax palette drawn from Okabe and Ito's canonical eight
hues. Token mapping uses canonical Okabe-Ito hex values throughout, leaning on bold and
italic typography to disambiguate where two kinds share a hue:

- {lit}`blue` → keywords and universe operators (both bold; context disambiguates)
- {lit}`bluishGreen` → defined names ({lit}`const`) and module/namespace paths
- {lit}`vermillion` → bound variables (italic), universe-level variables (italic), and
  sort formers ({lit}`Type`/{lit}`Prop`/{lit}`Sort`, bold)
- {lit}`reddishPurple` → string literals
- {lit}`orange` → numeric literals (universe-level numerics)
- body text + italic → doc comments

Okabe-Ito was designed for scientific visualization on white substrates and prioritizes
colorblind safety over WCAG contrast. Several canonical hues sit between 3:1 and 4.5:1 on
white; the per-theme accessibility check will flag them, and the suite-wide setting
`warnPerThemeAccessibility` can downgrade those warnings. The colorblind-distinguishability
property is preserved.
-/
@[manual_theme]
public def ManualTheme.beaconLight : ManualTheme :=
  lightChromeFields {
    CodeTheme.ink with
    name := "Beacon Light",
    sourceLink := some Color.Palettes.OkabeIto.sourceLink,
    keyword := { color := blue, weight := .bold, style := .normal, face := .mono },
    const := { color := bluishGreen, weight := .regular, style := .normal, face := .mono },
    «var» := { color := vermillion, weight := .regular, style := .italic, face := .mono },
    literal := { color := Color.black, weight := .regular, style := .normal, face := .mono },
    literalString := { color := reddishPurple, weight := .regular, style := .normal, face := .mono },
    -- Per the docstring's "orange → numeric literals": real number literals get orange too,
    -- not just `levelConst`. Character literals share the string hue.
    literalNumber := { color := orange, weight := .regular, style := .normal, face := .mono },
    literalChar := { color := reddishPurple, weight := .regular, style := .normal, face := .mono },
    docComment := { color := Color.black, weight := .regular, style := .italic, face := .mono },
    sort := { color := vermillion, weight := .bold, style := .normal, face := .mono },
    levelVar := { color := vermillion, weight := .regular, style := .italic, face := .mono },
    levelConst := { color := orange, weight := .regular, style := .normal, face := .mono },
    levelOp := { color := blue, weight := .bold, style := .normal, face := .mono },
    moduleName := { color := bluishGreen, weight := .regular, style := .normal, face := .mono }
  }

open Color.Palettes.OkabeIto in
/--
Beacon dark: a Verso-side adaptation of the Okabe-Ito palette to a near-black background.
Okabe and Ito designed the palette for scientific visualization on white substrates; the
upstream specification does not define a dark-substrate syntax theme, so the token-to-hue
mapping here is a Verso choice that preserves the canonical colorblind-distinguishability
property while picking which hue carries which token kind. {lit}`skyBlue` and {lit}`yellow`
carry the most-used kinds because they are brightest on dark substrates; typography (bold,
italic) disambiguates kinds that share a hue, the same way the light variant does.
-/
@[manual_theme]
public def ManualTheme.beaconDark : ManualTheme :=
  darkChromeFields {
    darkCodeBase with
    name := "Beacon Dark",
    sourceLink := some Color.Palettes.OkabeIto.sourceLink,
    keyword := { color := skyBlue, weight := .bold, style := .normal, face := .mono },
    const := { color := bluishGreen, weight := .regular, style := .normal, face := .mono },
    «var» := { color := orange, weight := .regular, style := .italic, face := .mono },
    literalString := { color := yellow, weight := .regular, style := .normal, face := .mono },
    -- Pair real number literals with `levelConst` on yellow; characters share the string hue.
    literalNumber := { color := yellow, weight := .regular, style := .normal, face := .mono },
    literalChar := { color := yellow, weight := .regular, style := .normal, face := .mono },
    sort := { color := reddishPurple, weight := .bold, style := .normal, face := .mono },
    levelVar := { color := orange, weight := .regular, style := .italic, face := .mono },
    levelConst := { color := yellow, weight := .regular, style := .normal, face := .mono },
    levelOp := { color := skyBlue, weight := .bold, style := .normal, face := .mono },
    moduleName := { color := bluishGreen, weight := .regular, style := .normal, face := .mono }
  }

/-! # Solarized — Ethan Schoonover's standard palette -/

open Color.Palettes.Solarized in
/--
Solarized light: Schoonover's standard cream-on-paper palette. Surface and foreground follow
the canonical rebasing rules — {lit}`base3` background, {lit}`base00` primary body content,
{lit}`base01` for emphasized content (headings, structural decoration), {lit}`base1` for
secondary content (comments and muted chrome text). Accent hues map per common port
conventions:

- {lit}`green` → keywords
- {lit}`blue` → defined names ({lit}`const`)
- {lit}`violet` → bound variables ({lit}`var`)
- {lit}`cyan` → string literals
- {lit}`base1` → doc comments (Solarized's documented muted secondary-content hue)
- {lit}`yellow` → {lit}`Type`/{lit}`Prop`/{lit}`Sort` formers
- {lit}`orange` → numeric literals (including universe-level numerics)
- {lit}`magenta` → universe operators ({lit}`max`, {lit}`imax`) and module/namespace paths

Solarized's documented comment color is base1, which is below WCAG AA 4.5 against base3
substrate by design; the per-theme accessibility check flags this and the suite-wide setting
`warnPerThemeAccessibility` can downgrade it.
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
      textColor := base00,
      codeColor := base00,
      -- Structural decoration (case labels) uses the canonical emphasized-content shade.
      structureColor := base01,
      warningColor := base00,
      infoColor := base00,
      errorColor := red,
      errorIndicatorColor := red,
      warningIndicatorColor := yellow,
      infoIndicatorColor := blue,
      hoverBackground := base2,
      hoverText := base00,
      hoverBorderColor := base1,
      hoverSeparatorColor := base1,
      tokenHighlightBackground := base2,
      tacticStateBorderColor := base1,
      selectedColor := base2,
      highlightOnCode := color%#f7e7a3,
      uiOnCode := base1,
      keyword := { color := green, weight := .bold, style := .normal, face := .mono },
      const := { color := blue, weight := .regular, style := .normal, face := .mono },
      «var» := { color := violet, weight := .regular, style := .italic, face := .mono },
      literal := { color := base00, weight := .regular, style := .normal, face := .mono },
      literalString := { color := cyan, weight := .regular, style := .normal, face := .mono },
      -- Numbers and characters → cyan, matching Solarized vim's `Number`/`Character` mapping
      -- (the `Constant` family). Operator → green (links to `Statement`).
      literalNumber := { color := cyan, weight := .regular, style := .normal, face := .mono },
      literalChar := { color := cyan, weight := .regular, style := .normal, face := .mono },
      operator := { color := green, weight := .regular, style := .normal, face := .mono },
      -- `delim`/`bracket`/`separator` are spelled out at base00 (Solarized Light's body
      -- code color). Without these, `CodeTheme.ink with` would leave them frozen at Ink's
      -- black `codeColor`.
      delim := { color := base00, weight := .regular, style := .normal, face := .mono },
      bracket := { color := base00, weight := .regular, style := .normal, face := .mono },
      separator := { color := base00, weight := .regular, style := .normal, face := .mono },
      docComment := { color := base1, weight := .regular, style := .italic, face := .mono },
      -- Comments → base1, Solarized's documented "secondary content" shade on the light
      -- substrate. This is intentionally sub-AA per the spec (Schoonover's contrast trade-off
      -- to background-out commentary); the per-theme accessibility check flags it.
      comment := { color := base1, weight := .regular, style := .italic, face := .mono },
      commentDelim := { color := base1, weight := .regular, style := .italic, face := .mono },
      sort := { color := yellow, weight := .regular, style := .normal, face := .mono },
      levelVar := { color := violet, weight := .regular, style := .italic, face := .mono },
      levelConst := { color := cyan, weight := .regular, style := .normal, face := .mono },
      levelOp := { color := green, weight := .regular, style := .normal, face := .mono },
      moduleName := { color := magenta, weight := .regular, style := .normal, face := .mono }
    },
    surfaceColor := base2,
    tocBackground := base2,
    borderColor := base01,
    -- Muted chrome text uses Solarized's "secondary content" shade.
    mutedColor := base1,
    linkColor := blue,
    visitedLinkColor := violet,
    burgerVisibleShadowColor := base3,
    burgerHiddenColor := base01,
    burgerHiddenShadowColor := base3,
    licenses := #[Verso.Genre.Manual.Licenses.solarized]
  }

open Color.Palettes.Solarized in
/--
Solarized dark: Schoonover's standard {lit}`base03` background. Surface and foreground follow
the canonical rebasing rules — {lit}`base03` background, {lit}`base0` primary body content,
{lit}`base1` for emphasized content (headings, structural decoration), {lit}`base01` for
secondary content (comments and muted chrome text). Token accent assignments match
{Lean.Doc.name}`ManualTheme.solarizedLight`; the relative-luminance jump comes entirely from
the substrate.
-/
@[manual_theme]
public def ManualTheme.solarizedDark : ManualTheme :=
  { darkChromeFields {
    darkCodeBase with
    name := s!"{Color.Palettes.Solarized.name} Dark",
    sourceLink := some Color.Palettes.Solarized.sourceLink,
    background := base03,
    codeBlockBackground := base02,
    textColor := base0,
    codeColor := base0,
    -- Structural decoration uses the canonical emphasized-content shade.
    structureColor := base1,
    warningColor := base0,
    infoColor := base0,
    errorColor := red,
    errorIndicatorColor := red,
    warningIndicatorColor := yellow,
    infoIndicatorColor := blue,
    hoverBackground := base02,
    hoverText := base0,
    hoverBorderColor := base01,
    hoverSeparatorColor := base01,
    tokenHighlightBackground := base02,
    tacticStateBorderColor := base01,
    selectedColor := base02,
    highlightOnCode := color%#3a2f00,
    uiOnCode := base01,
    keyword := { color := green, weight := .bold, style := .normal, face := .mono },
    const := { color := blue, weight := .regular, style := .normal, face := .mono },
    «var» := { color := violet, weight := .regular, style := .italic, face := .mono },
    literal := { color := base0, weight := .regular, style := .normal, face := .mono },
    literalString := { color := cyan, weight := .regular, style := .normal, face := .mono },
    -- Spec-aligned: cyan for Number/Character, green for Operator. See `solarizedLight`
    -- for the same role rationale.
    literalNumber := { color := cyan, weight := .regular, style := .normal, face := .mono },
    literalChar := { color := cyan, weight := .regular, style := .normal, face := .mono },
    operator := { color := green, weight := .regular, style := .normal, face := .mono },
    -- `delim`/`bracket`/`separator` spelled out at base0 (Solarized Dark's body code
    -- color). `darkCodeBase with` leaves them at the generic dark base's `#e8e8e8`
    -- otherwise — readable but off-palette.
    delim := { color := base0, weight := .regular, style := .normal, face := .mono },
    bracket := { color := base0, weight := .regular, style := .normal, face := .mono },
    separator := { color := base0, weight := .regular, style := .normal, face := .mono },
    docComment := { color := base01, weight := .regular, style := .italic, face := .mono },
    comment := { color := base01, weight := .regular, style := .italic, face := .mono },
    commentDelim := { color := base01, weight := .regular, style := .italic, face := .mono },
    sort := { color := yellow, weight := .regular, style := .normal, face := .mono },
    levelVar := { color := violet, weight := .regular, style := .italic, face := .mono },
    levelConst := { color := cyan, weight := .regular, style := .normal, face := .mono },
    levelOp := { color := green, weight := .regular, style := .normal, face := .mono },
    moduleName := { color := magenta, weight := .regular, style := .normal, face := .mono }
  } with
    -- Solarized-tinted chrome instead of the generic dark-chrome accents.
    surfaceColor := base02,
    tocBackground := base02,
    borderColor := base01,
    mutedColor := base01,
    linkColor := blue,
    visitedLinkColor := violet,
    burgerHiddenColor := base0,
    burgerVisibleColor := base0,
    burgerHiddenShadowColor := base03,
    burgerVisibleShadowColor := base03,
    licenses := #[Verso.Genre.Manual.Licenses.solarized] }

/-! # Nord — Sven Greb's arctic, north-bluish palette -/

open Color.Palettes.Nord in
/--
Nord: the canonical Nord palette on its Polar Night substrate ({lit}`nord0` page, {lit}`nord1`
code blocks). Token mapping follows Nord's documented hue intent:

- {lit}`nord9` ("keywords, support, operators, tags") → {lit}`keyword`
- {lit}`nord8` ("declarations, calls, execution statements") → {lit}`const`
- {lit}`nord4` ("syntax variables and constants") → {lit}`var`, with italic
- {lit}`nord14` ("string syntax highlighting") → {lit}`literalString`
- {lit}`nord3` ("comments") → {lit}`docComment`
- {lit}`nord7` ("classes, types, and primitives") → {lit}`sort` and {lit}`moduleName`
- {lit}`nord10` ("pragmas, preprocessor") → {lit}`levelOp` (universe-grammar built-ins)
- {lit}`nord15` ("numbers, floating-point literals") → {lit}`levelConst`
- {lit}`nord9` ("operators, support, tags") → {lit}`operator` (symbolic operators like
  {lit}`+`, {lit}`::`, {lit}`>>=`). The built-in {lit}`delim` family stays on body color:
  SubVerso bundles type ascription {lit}`:` and pattern alternative {lit}`|` into
  {lit}`.delim` alongside {lit}`:=`/{lit}`=>`, and applying a syntax accent to every typed
  binder would be visually heavy. {lit}`bracket` and {lit}`separator` cascade from
  {lit}`delim` and also land on body color, matching the Nord spec's silence on these.
-/
@[manual_theme]
public def ManualTheme.nord : ManualTheme :=
  { darkChromeFields {
      CodeTheme.ink with
      name := Color.Palettes.Nord.name,
      sourceLink := some Color.Palettes.Nord.sourceLink,
      appearance := .dark,
      background := nord0,
      codeBlockBackground := nord1,
      textColor := nord4,
      codeColor := nord4,
      structureColor := nord4,
      warningColor := nord4,
      infoColor := nord4,
      errorColor := nord11,
      errorIndicatorColor := nord11,
      warningIndicatorColor := nord13,
      infoIndicatorColor := nord8,
      const := { color := nord8, weight := .regular, style := .normal, face := .mono },
      keyword := { color := nord9, weight := .bold, style := .normal, face := .mono },
      «var» := { color := nord4, weight := .regular, style := .italic, face := .mono },
      literal := { color := nord4, weight := .regular, style := .normal, face := .mono },
      literalString := { color := nord14, weight := .regular, style := .normal, face := .mono },
      docComment := { color := nord3, weight := .regular, style := .italic, face := .mono },
      sort := { color := nord7, weight := .regular, style := .normal, face := .mono },
      levelVar := { color := nord4, weight := .regular, style := .italic, face := .mono },
      levelConst := { color := nord15, weight := .regular, style := .normal, face := .mono },
      levelOp := { color := nord10, weight := .regular, style := .normal, face := .mono },
      moduleName := { color := nord7, weight := .regular, style := .normal, face := .mono },
      -- Symbolic operators → nord9, the Nord syntax doc's "operators, support, tags" slot.
      -- `delim`, `bracket`, and `separator` ride on nord4 (the body color): `.delim` bundles
      -- `:` and `|` with `:=`/`=>`, and painting them nord9 would put a syntax accent on every
      -- typed binder. These are spelled out because `CodeTheme.ink with` doesn't re-evaluate
      -- the cascade defaults — they'd otherwise stay frozen at Ink's black `codeColor`.
      delim := { color := nord4, weight := .regular, style := .normal, face := .mono },
      operator := { color := nord9, weight := .regular, style := .normal, face := .mono },
      bracket := { color := nord4, weight := .regular, style := .normal, face := .mono },
      separator := { color := nord4, weight := .regular, style := .normal, face := .mono },
      -- Per the Nord syntax doc: nord15 ("numbers, floating-point literals") → numbers;
      -- chars share nord14 with strings (no separate slot); nord3 ("comments / indent
      -- guides") → ordinary line and block comments and their delimiters.
      literalNumber := { color := nord15, weight := .regular, style := .normal, face := .mono },
      literalChar := { color := nord14, weight := .regular, style := .normal, face := .mono },
      comment := { color := nord3, weight := .regular, style := .normal, face := .mono },
      commentDelim := { color := nord3, weight := .regular, style := .normal, face := .mono },
      hoverBackground := nord2,
      hoverText := nord4,
      hoverBorderColor := nord3,
      hoverSeparatorColor := nord3,
      tokenHighlightBackground := nord2,
      tacticStateBorderColor := nord3,
      selectedColor := nord2,
      highlightOnCode := nord3,
      highlightOnText := nord3,
      uiOnCode := nord3
    } with
      surfaceColor := nord1,
      tocBackground := nord0,
      borderColor := nord3,
      mutedColor := nord4,
      linkColor := nord8,
      visitedLinkColor := nord15,
      licenses := #[Verso.Genre.Manual.Licenses.nord] }

open Color.Palettes.Nord in
/--
Nord Light: Nord's bright-ambiance configuration as documented by the upstream spec —
{lit}`nord6` as page background, {lit}`nord5` as the selection / active-line /
text-highlight color, {lit}`nord0` as the plain syntax text color. Token accent assignments
mirror the dark variant: the canonical Nord Frost and Aurora hues drive
keyword/const/string/sort/etc., per Nord's documented per-color usage table.

The spec does not explicitly designate a bright-ambiance color for syntax variables
({lit}`nord4` is reserved for the dark-ambiance variable hue and is illegible on {lit}`nord6`),
so {lit}`nord3` (Polar Night, documented "comments / indent guides") is reused with italic for
{lit}`var`/{lit}`levelVar`/{lit}`docComment` — a pragmatic choice, not an upstream mapping.

Several canonical Nord token colors — Frost {lit}`nord7`–{lit}`nord9` and Aurora
{lit}`nord13`/{lit}`nord14` — fall below WCAG AA 4.5 against {lit}`nord6`. The per-theme
accessibility check flags these and the suite-wide setting `warnPerThemeAccessibility` can
downgrade them. The canonical hex values are preserved so the look matches other Nord Light
ports.
-/
@[manual_theme]
public def ManualTheme.nordLight : ManualTheme where
  toCodeTheme := {
    CodeTheme.ink with
    name := s!"{Color.Palettes.Nord.name} Light",
    sourceLink := some Color.Palettes.Nord.sourceLink,
    background := nord6,
    codeBlockBackground := nord5,
    textColor := nord0,
    codeColor := nord0,
    structureColor := nord0,
    warningColor := nord0,
    infoColor := nord0,
    errorColor := nord11,
    errorIndicatorColor := nord11,
    warningIndicatorColor := nord13,
    infoIndicatorColor := nord10,
    hoverBackground := nord5,
    hoverText := nord0,
    hoverBorderColor := nord3,
    hoverSeparatorColor := nord3,
    tokenHighlightBackground := nord5,
    tacticStateBorderColor := nord3,
    -- Per the Nord spec, `nord5` is the documented bright-ambiance selection / text-highlight
    -- color.
    selectedColor := nord5,
    highlightOnCode := nord5,
    uiOnCode := nord3,
    -- Canonical Nord token mapping. `var`/`levelVar`/`docComment` reuse `nord3` (the
    -- documented "comments / indent guides" color) because the spec does not designate a
    -- bright-ambiance variable hue and `nord4` (the dark-mode variable color) is illegible
    -- on `nord6`.
    keyword := { color := nord9, weight := .bold, style := .normal, face := .mono },
    const := { color := nord8, weight := .regular, style := .normal, face := .mono },
    «var» := { color := nord3, weight := .regular, style := .italic, face := .mono },
    literal := { color := nord0, weight := .regular, style := .normal, face := .mono },
    literalString := { color := nord14, weight := .regular, style := .normal, face := .mono },
    docComment := { color := nord3, weight := .regular, style := .italic, face := .mono },
    sort := { color := nord7, weight := .regular, style := .normal, face := .mono },
    levelVar := { color := nord3, weight := .regular, style := .italic, face := .mono },
    levelConst := { color := nord15, weight := .regular, style := .normal, face := .mono },
    levelOp := { color := nord10, weight := .regular, style := .normal, face := .mono },
    moduleName := { color := nord7, weight := .regular, style := .normal, face := .mono },
    -- Symbolic operators → nord9 (the Nord syntax doc's "operators, support, tags" slot).
    -- `delim`/`bracket`/`separator` ride on nord0 (the body code color). See
    -- `ManualTheme.nord` for the rationale and the `with`-doesn't-re-evaluate-defaults note.
    delim := { color := nord0, weight := .regular, style := .normal, face := .mono },
    operator := { color := nord9, weight := .regular, style := .normal, face := .mono },
    bracket := { color := nord0, weight := .regular, style := .normal, face := .mono },
    separator := { color := nord0, weight := .regular, style := .normal, face := .mono },
    -- Same per-spec role assignments as the dark variant: nord15 numbers, nord14 chars,
    -- nord3 comments.
    literalNumber := { color := nord15, weight := .regular, style := .normal, face := .mono },
    literalChar := { color := nord14, weight := .regular, style := .normal, face := .mono },
    comment := { color := nord3, weight := .regular, style := .normal, face := .mono },
    commentDelim := { color := nord3, weight := .regular, style := .normal, face := .mono }
  }
  surfaceColor := nord5
  tocBackground := nord5
  borderColor := nord3
  mutedColor := nord3
  linkColor := nord10
  visitedLinkColor := nord15
  burgerVisibleShadowColor := nord6
  burgerHiddenColor := nord0
  burgerHiddenShadowColor := nord6
  licenses := #[Verso.Genre.Manual.Licenses.nord]

/-! # Dracula and Alucard — Dracula spec palettes -/

open Color.Palettes.DraculaClassic in
/--
Dracula: the canonical dark Dracula palette from the official spec. Token mapping follows
the spec's documented hue roles:

- Pink ("Keywords, Storage Types"): {lit}`keyword`, the symbolic-operator bucket
  {lit}`operator` ({lit}`+`, {lit}`::`, {lit}`>>=`, …), and the universe operators
  {lit}`max` / {lit}`imax` / {lit}`+` via {lit}`levelOp`. Built-in delimiters are *not*
  painted Pink because SubVerso's {lit}`delim` kind also covers the type-ascription
  {lit}`:` and the pattern-alternative {lit}`|`; applying a syntax accent there would
  cost every typed binder a heavy color, which no Dracula port does.
- Cyan ("Classes, Types, Support, Regular Expressions"): {lit}`sort` ({lit}`Type`,
  {lit}`Prop`, {lit}`Sort u`) and {lit}`moduleName` (namespace paths in {lit}`import` lines).
- Green ("Functions, Methods, Inherited Classes"): {lit}`const` — Lean's named-constant
  references are largely function and definition names.
- Yellow ("Strings, Text Content"): {lit}`literalString` and {lit}`literalChar` (the
  Dracula spec does not give characters a separate slot).
- Orange ("Numbers, Constants, Booleans"): {lit}`literalNumber`, {lit}`levelConst` (universe
  numerals), and the boolean {lit}`Bool.true` / {lit}`Bool.false` (still surfaced through
  {lit}`extraCss` until SubVerso classifies booleans).
- Red ("Errors, Warnings, Deletions"): {lit}`errorColor` / {lit}`errorIndicatorColor`.
- Comment ("Comments and disabled code"): {lit}`docComment` plus the new {lit}`comment` /
  {lit}`commentDelim` fields for ordinary {lit}`--` and {lit}`/- … -/` comments.
- Foreground: bound variables ({lit}`var`, {lit}`levelVar`), the built-in delimiter family
  ({lit}`delim` — {lit}`:=`, {lit}`=>`, {lit}`:`, {lit}`|`, …), and the {lit}`bracket` /
  {lit}`separator` punctuation buckets, since the Dracula spec does not assign a syntax
  color to any of these and SubVerso's {lit}`.delim` is too coarse to single out the
  binding-marker subset.

Purple ("Instance reserved words and Constants") has no Lean syntax analog (no "instance
reserved words"; the constants slot is already covered by {lit}`const` on Green), so the
palette uses it as a chrome accent for visited links rather than for any token kind.
-/
@[manual_theme]
public def ManualTheme.dracula : ManualTheme :=
  let code : CodeTheme := {
    darkCodeBase with
    name := Color.Palettes.DraculaClassic.name,
    sourceLink := some Color.Palettes.DraculaClassic.sourceLink,
    background := background,
    codeBlockBackground := background,
    textColor := foreground,
    codeColor := foreground,
    structureColor := foreground,
    warningColor := foreground,
    infoColor := foreground,
    errorColor := red,
    errorIndicatorColor := red,
    warningIndicatorColor := orange,
    infoIndicatorColor := cyan,
    -- Hover popups land on the Selection color so they read as a raised surface tied to
    -- the same palette.
    hoverBackground := selection,
    hoverText := foreground,
    hoverBorderColor := currentLine,
    hoverSeparatorColor := currentLine,
    tokenHighlightBackground := selection,
    tacticStateBackground := background,
    tacticStateBorderColor := currentLine,
    selectedColor := selection,
    highlightOnCode := selection,
    highlightOnText := selection,
    uiOnCode := currentLine,
    -- Token mapping per the Dracula spec's documented roles.
    keyword.color := pink,
    const.color := green,
    «var».color := foreground,
    literalString.color := yellow,
    docComment.color := comment,
    -- Sort formers (`Type`, `Prop`, `Sort u`) → Cyan, the spec's "Classes, Types, Support"
    -- slot.
    sort := { color := cyan, weight := .regular, style := .normal, face := .mono },
    -- Universe operators (`max`, `imax`, `+` at the level grammar) → Pink, joining the
    -- "Keywords, Storage Types" / operator family.
    levelOp := { color := pink, weight := .regular, style := .normal, face := .mono },
    -- Universe variables stay quiet (parallel to value-level `var`): body text, italic.
    levelVar := { color := foreground, weight := .regular, style := .italic, face := .mono },
    -- Numeric universe constants get the Orange "numbers" slot.
    levelConst := { color := orange, weight := .regular, style := .normal, face := .mono },
    -- Namespace paths land on Cyan ("classes, types, support").
    moduleName := { color := cyan, weight := .regular, style := .normal, face := .mono },
    -- Symbolic operators (`+`, `::`, `>>=`, …) → Pink, joining the "Keywords, Storage Types"
    -- family. `delim` stays on the body foreground (cascade default) because SubVerso bundles
    -- `:` and `|` into `.delim` alongside `:=`/`=>`, and painting every typed binder Pink
    -- would be too heavy; `bracket` and `separator` cascade from `delim` and so also land on
    -- foreground, matching Dracula's convention of leaving brackets and item separators
    -- unstyled.
    operator := { color := pink, weight := .regular, style := .normal, face := .mono },
    -- Numbers → Orange ("Numbers, Constants, Booleans"). Chars share Yellow with strings
    -- (Dracula does not give characters a distinct slot). Comments and their delimiters →
    -- Dracula's Comment color (a soft steel-blue), no italic — italic is reserved for
    -- doc comments in our default rendering. `commentDelim` is spelled out explicitly: the
    -- `comment := comment` cascade was frozen at `CodeTheme.ink`'s black `codeColor` when
    -- this struct was constructed, so a bare `comment` override wouldn't reach it.
    literalNumber := { color := orange, weight := .regular, style := .normal, face := .mono },
    literalChar := { color := yellow, weight := .regular, style := .normal, face := .mono },
    comment := { color := comment, weight := .regular, style := .normal, face := .mono },
    commentDelim := { color := comment, weight := .regular, style := .normal, face := .mono },
    -- The Dracula spec gives Orange to "numbers, constants, booleans". Verso doesn't yet have
    -- a numeric-literal kind from the highlighter, but the `const` tokens for `Bool.true` and
    -- `Bool.false` carry a `data-binding` attribute the highlighter emits, so a CSS attribute
    -- selector can override their `const`-green color to the boolean Orange. When SubVerso
    -- gains a numeric kind, the same trick (or a new `literal.number` rule) extends the same
    -- treatment to integer literals.
    extraCss := fun _ =>
      ".hl.lean .const[data-binding=\"const-Bool.true\"],\n" ++
      ".hl.lean .const[data-binding=\"const-Bool.false\"] { color: " ++ Color.css orange ++ "; }\n"
  }
  { darkChromeFields code with
    -- Override the generic dark chrome with Dracula-palette values.
    surfaceColor := selection,
    tocBackground := background,
    borderColor := currentLine,
    mutedColor := comment,
    linkColor := cyan,
    visitedLinkColor := purple,
    burgerVisibleShadowColor := background,
    burgerHiddenColor := foreground,
    burgerHiddenShadowColor := background,
    licenses := #[Verso.Genre.Manual.Licenses.dracula] }

open Color.Palettes.AlucardClassic in
/--
Alucard: the canonical light counterpart to Dracula from the official spec. Same documented
token roles as {Lean.Doc.name}`ManualTheme.dracula`, drawn from the Alucard hex values
(deeper saturations so each token meets WCAG AA contrast on the cream background).
-/
@[manual_theme]
public def ManualTheme.alucard : ManualTheme where
  toCodeTheme := {
    CodeTheme.ink with
    name := Color.Palettes.AlucardClassic.name,
    sourceLink := some Color.Palettes.AlucardClassic.sourceLink,
    background := background,
    codeBlockBackground := background,
    textColor := foreground,
    codeColor := foreground,
    structureColor := foreground,
    warningColor := foreground,
    infoColor := foreground,
    errorColor := red,
    errorIndicatorColor := red,
    warningIndicatorColor := orange,
    infoIndicatorColor := cyan,
    hoverBackground := selection,
    hoverText := foreground,
    hoverBorderColor := currentLine,
    hoverSeparatorColor := currentLine,
    tokenHighlightBackground := selection,
    tacticStateBorderColor := currentLine,
    selectedColor := selection,
    highlightOnCode := selection,
    uiOnCode := currentLine,
    keyword.color := pink,
    const.color := green,
    «var».color := foreground,
    literalString.color := yellow,
    docComment.color := comment,
    -- Sort formers (`Type`, `Prop`, `Sort u`) → Cyan, the spec's "Classes, Types, Support"
    -- slot. See `ManualTheme.dracula` for the rationale shared with the dark variant.
    sort := { color := cyan, weight := .regular, style := .normal, face := .mono },
    -- Universe operators (`max`, `imax`, `+`) → Pink, the spec's keyword/operator family.
    levelOp := { color := pink, weight := .regular, style := .normal, face := .mono },
    levelVar := { color := foreground, weight := .regular, style := .italic, face := .mono },
    levelConst := { color := orange, weight := .regular, style := .normal, face := .mono },
    moduleName := { color := cyan, weight := .regular, style := .normal, face := .mono },
    -- Symbolic operators → Pink. `delim`/`bracket`/`separator` are spelled out at the
    -- Alucard foreground rather than relying on the cascade default: `CodeTheme.ink with`
    -- doesn't re-evaluate the `{ color := codeColor, ... }` cascades, so without these
    -- explicit overrides they'd stay frozen at Ink's black `codeColor`.
    delim := { color := foreground, weight := .regular, style := .normal, face := .mono },
    operator := { color := pink, weight := .regular, style := .normal, face := .mono },
    bracket := { color := foreground, weight := .regular, style := .normal, face := .mono },
    separator := { color := foreground, weight := .regular, style := .normal, face := .mono },
    -- Numbers → Orange; chars → Yellow (same as strings); comments and their delimiters →
    -- Alucard's Comment color. Same role assignments as the dark variant.
    literalNumber := { color := orange, weight := .regular, style := .normal, face := .mono },
    literalChar := { color := yellow, weight := .regular, style := .normal, face := .mono },
    comment := { color := comment, weight := .regular, style := .normal, face := .mono },
    commentDelim := { color := comment, weight := .regular, style := .normal, face := .mono },
    -- Same boolean-orange trick as the dark variant; see the Dracula def for the rationale.
    extraCss := fun _ =>
      ".hl.lean .const[data-binding=\"const-Bool.true\"],\n" ++
      ".hl.lean .const[data-binding=\"const-Bool.false\"] { color: " ++ Color.css orange ++ "; }\n"
  }
  surfaceColor := selection
  tocBackground := background
  borderColor := currentLine
  mutedColor := comment
  linkColor := cyan
  visitedLinkColor := purple
  burgerVisibleShadowColor := background
  burgerHiddenColor := foreground
  burgerHiddenShadowColor := background
  licenses := #[Verso.Genre.Manual.Licenses.dracula]

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
    «var».color := color%#3b2a17,
    -- Spell out the punctuation, literal, and comment families at the Sandstone body
    -- color so `CodeTheme.ink with` doesn't leave them frozen at Ink's black `codeColor`.
    delim := { color := color%#3b2a17, weight := .regular, style := .normal, face := .mono },
    operator := { color := color%#3b2a17, weight := .regular, style := .normal, face := .mono },
    bracket := { color := color%#3b2a17, weight := .regular, style := .normal, face := .mono },
    separator := { color := color%#3b2a17, weight := .regular, style := .normal, face := .mono },
    literalNumber := { color := color%#3b2a17, weight := .regular, style := .normal, face := .mono },
    literalChar := { color := color%#3b2a17, weight := .regular, style := .normal, face := .mono },
    comment := { color := color%#3b2a17, weight := .regular, style := .normal, face := .mono },
    commentDelim := { color := color%#3b2a17, weight := .regular, style := .normal, face := .mono }
  }
  surfaceColor := color%#f3e9d6
  tocBackground := color%#f3e9d6
  borderColor := color%#8c7257
  mutedColor := color%#7a5a40
  linkColor := color%#a04a00
  visitedLinkColor := color%#7a3a91
  burgerVisibleShadowColor := color%#faf5ee
  burgerHiddenColor := color%#3b2a17
  burgerHiddenShadowColor := color%#faf5ee

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
    «var».color := color%#f3d5a3,
    -- Align punctuation, literals, and comments with the Sandstone Dark sunlit-buff body
    -- color rather than `darkCodeBase`'s generic `#e8e8e8`.
    delim := { color := color%#f3d5a3, weight := .regular, style := .normal, face := .mono },
    operator := { color := color%#f3d5a3, weight := .regular, style := .normal, face := .mono },
    bracket := { color := color%#f3d5a3, weight := .regular, style := .normal, face := .mono },
    separator := { color := color%#f3d5a3, weight := .regular, style := .normal, face := .mono },
    literalNumber := { color := color%#f3d5a3, weight := .regular, style := .normal, face := .mono },
    literalChar := { color := color%#f3d5a3, weight := .regular, style := .normal, face := .mono },
    comment := { color := color%#f3d5a3, weight := .regular, style := .normal, face := .mono },
    commentDelim := { color := color%#f3d5a3, weight := .regular, style := .normal, face := .mono }
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
    «var».color := color%#0e2431,
    -- Spell out the punctuation, literal, and comment families at the Steel deep-navy body
    -- color so `CodeTheme.ink with` doesn't leave them frozen at Ink's black `codeColor`.
    delim := { color := color%#0e2431, weight := .regular, style := .normal, face := .mono },
    operator := { color := color%#0e2431, weight := .regular, style := .normal, face := .mono },
    bracket := { color := color%#0e2431, weight := .regular, style := .normal, face := .mono },
    separator := { color := color%#0e2431, weight := .regular, style := .normal, face := .mono },
    literalNumber := { color := color%#0e2431, weight := .regular, style := .normal, face := .mono },
    literalChar := { color := color%#0e2431, weight := .regular, style := .normal, face := .mono },
    comment := { color := color%#0e2431, weight := .regular, style := .normal, face := .mono },
    commentDelim := { color := color%#0e2431, weight := .regular, style := .normal, face := .mono }
  }
  surfaceColor := color%#e3e8ee
  tocBackground := color%#e3e8ee
  borderColor := color%#46566a
  mutedColor := color%#465a70
  linkColor := color%#1a5ea8
  visitedLinkColor := color%#6c4ea8
  burgerVisibleShadowColor := color%#f4f6f8
  burgerHiddenColor := color%#0e2431
  burgerHiddenShadowColor := color%#f4f6f8

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
    «var».color := color%#dfe6ee,
    -- Align punctuation, literals, and comments with the Slate body color so they don't
    -- inherit `darkCodeBase`'s generic `#e8e8e8` (close, but off-palette).
    delim := { color := color%#dfe6ee, weight := .regular, style := .normal, face := .mono },
    operator := { color := color%#dfe6ee, weight := .regular, style := .normal, face := .mono },
    bracket := { color := color%#dfe6ee, weight := .regular, style := .normal, face := .mono },
    separator := { color := color%#dfe6ee, weight := .regular, style := .normal, face := .mono },
    literalNumber := { color := color%#dfe6ee, weight := .regular, style := .normal, face := .mono },
    literalChar := { color := color%#dfe6ee, weight := .regular, style := .normal, face := .mono },
    comment := { color := color%#dfe6ee, weight := .regular, style := .normal, face := .mono },
    commentDelim := { color := color%#dfe6ee, weight := .regular, style := .normal, face := .mono }
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
    «var».color := color%#3d2f1f,
    -- Spell out the punctuation, literal, and comment families at the Hearth body color so
    -- `CodeTheme.ink with` doesn't leave them frozen at Ink's black `codeColor`.
    delim := { color := color%#3d2f1f, weight := .regular, style := .normal, face := .mono },
    operator := { color := color%#3d2f1f, weight := .regular, style := .normal, face := .mono },
    bracket := { color := color%#3d2f1f, weight := .regular, style := .normal, face := .mono },
    separator := { color := color%#3d2f1f, weight := .regular, style := .normal, face := .mono },
    literalNumber := { color := color%#3d2f1f, weight := .regular, style := .normal, face := .mono },
    literalChar := { color := color%#3d2f1f, weight := .regular, style := .normal, face := .mono },
    comment := { color := color%#3d2f1f, weight := .regular, style := .normal, face := .mono },
    commentDelim := { color := color%#3d2f1f, weight := .regular, style := .normal, face := .mono }
  }
  textFace := .serif
  structureFace := .serif
  surfaceColor := color%#ede4cf
  tocBackground := color%#ede4cf
  borderColor := color%#7a6952
  mutedColor := color%#6b5640
  linkColor := color%#2f6e58
  visitedLinkColor := color%#7a3a91
  burgerVisibleShadowColor := color%#f7f1de
  burgerHiddenColor := color%#3d2f1f
  burgerHiddenShadowColor := color%#f7f1de

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
    «var».color := color%#f1e7d2,
    -- Align punctuation, literals, and comments with the Hearth Dark candlelit-cream body
    -- color rather than `darkCodeBase`'s generic `#e8e8e8`.
    delim := { color := color%#f1e7d2, weight := .regular, style := .normal, face := .mono },
    operator := { color := color%#f1e7d2, weight := .regular, style := .normal, face := .mono },
    bracket := { color := color%#f1e7d2, weight := .regular, style := .normal, face := .mono },
    separator := { color := color%#f1e7d2, weight := .regular, style := .normal, face := .mono },
    literalNumber := { color := color%#f1e7d2, weight := .regular, style := .normal, face := .mono },
    literalChar := { color := color%#f1e7d2, weight := .regular, style := .normal, face := .mono },
    comment := { color := color%#f1e7d2, weight := .regular, style := .normal, face := .mono },
    commentDelim := { color := color%#f1e7d2, weight := .regular, style := .normal, face := .mono }
  }
  { base with textFace := .serif, structureFace := .serif }
