/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public meta import VersoManual.Theme.Ext
public import Verso.Theme.Code
public import VersoManual.LicenseInfo
public meta import Lean.Elab.Term

set_option linter.missingDocs true
set_option doc.verso true

/-!
The manual genre's theme. {lit}`ManualTheme` extends {lit}`CodeTheme` with the additional color
and font fields the manual chrome (page, header, ToC, search box, burger menu, content links)
needs. The manual genre emits every {lit}`--verso-*` chrome variable from a single chosen manual
theme.
-/

open Lean (Name)
open Verso.Genre.Manual

namespace Verso.Theme

/--
A manual-genre theme: a {name}`CodeTheme` plus the color and font fields the
chrome needs (header background, ToC, burger menu, search box, content links). Defaults reproduce
today's chrome.

The cascade rule from {name}`CodeTheme` continues: a field that today reads
the page background or text color defaults from the inherited field, so overriding the inherited
field carries through.
-/
public structure ManualTheme extends CodeTheme where
  /-- The font used for body prose. -/
  textFace : Typeface := .sans
  /-- The font used for headings, the ToC, navigation, and other structural text. -/
  structureFace : Typeface := .sans

  /-- A raised chrome surface tint (default for the ToC background and the search box). -/
  surfaceColor : Color := color%#f8f9fa
  /-- The header bar background. Defaults to the page background. -/
  headerBackground : Color := background
  /-- The ToC background. -/
  tocBackground : Color := color%#fafafa

  /--
  The default border color for chrome elements such as the search box outline. Defaults to
  a slate gray that clears WCAG 1.4.11 (3:1) against both white and the surface color.
  -/
  borderColor : Color := color%#878787
  /-- The default muted text color for chrome elements such as search hints. -/
  mutedColor : Color := color%#777777
  /-- The color used to highlight matched search terms. Defaults to the code theme's selection. -/
  highlightColor : Color := selectedColor

  /-- The color of content links in body prose. -/
  linkColor : Color := color%#0066cc
  /-- The color of visited content links. -/
  visitedLinkColor : Color := linkColor

  /-- The text color used inside the ToC. -/
  tocTextColor : Color := textColor

  /-- The color of the burger-menu lines while the ToC is visible. -/
  burgerVisibleColor : Color := tocTextColor
  /-- The shadow color drawn under the burger-menu lines while the ToC is visible. -/
  burgerVisibleShadowColor : Color := Color.white
  /-- The color of the burger-menu lines while the ToC is hidden. -/
  burgerHiddenColor : Color := color%#0e2431
  /-- The shadow color drawn under the burger-menu lines while the ToC is hidden. -/
  burgerHiddenShadowColor : Color := Color.white

  /--
  Third-party licenses the theme draws on (color palettes, fonts, etc.).
  -/
  licenses : Array LicenseInfo := #[]

/-! # Attribute and materialization -/

public section

/--
Attribute that registers a {name}`ManualTheme` declaration as an available theme. The
declaration must be in the current module (not imported), and its registration name is the decl's
name with macro scopes erased.
-/
syntax (name := manual_theme) "manual_theme" : attr

open Lean in
meta initialize
  registerBuiltinAttribute {
    name := `manual_theme,
    ref := by exact decl_name%,
    add := fun decl _stx kind => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'manual_theme', must be global"
      unless ((← getEnv).getModuleIdxFor? decl).isNone do
        throwError "invalid attribute 'manual_theme', declaration is in an imported module"
      modifyEnv fun env => manualThemeExt.addEntry env decl.eraseMacroScopes
    descr := "Registers a definition as an available manual theme"
  }

end section

/--
A materialized table of registered {name}`ManualTheme` values, keyed by registration
name. Built at runtime by the {lit}`manual_themes%` term elaborator from the set of
{name}`ManualTheme` declarations tagged with the {lit}`@[manual_theme]` attribute.
-/
public structure ManualThemeTable where
  /-- The map from a theme's registration name to its value. -/
  themes : Lean.NameMap ManualTheme := {}

namespace ManualThemeTable

/-- The empty table. -/
public def empty : ManualThemeTable := {}

public instance : EmptyCollection ManualThemeTable := ⟨empty⟩

/-- Looks up a theme by its registration name. -/
public def find? (t : ManualThemeTable) (n : Name) : Option ManualTheme :=
  t.themes.find? n

/-- Inserts a theme under the given registration name. -/
public def insert (t : ManualThemeTable) (n : Name) (theme : ManualTheme) : ManualThemeTable :=
  ⟨t.themes.insert n theme⟩

/-- Builds a table from a list of pairs. -/
public def fromList (xs : List (Name × ManualTheme)) : ManualThemeTable :=
  xs.foldl (fun (acc : ManualThemeTable) (p : Name × ManualTheme) => acc.insert p.1 p.2) empty

end ManualThemeTable

/--
The active set of themes resolved for a build: the registered table filtered by the
manual genre's {lit}`availableThemes` config, with the configured defaults auto-included.
Flows through the emit pipeline via a {lean}`ReaderT` layer in the manual genre's
{lit}`EmitM` rather than as a config field, since it is build-time state not user-authored
configuration.

Modeled as a {lean}`Lean.NameMap` so lookups are O(log n) and iteration is in stable name
order across builds.
-/
public abbrev ThemeRegistry : Type := Lean.NameMap ManualTheme

public section

/-- Term elaborator that materializes the registered manual-theme table at compile time. -/
syntax (name := manual_themes) "manual_themes%" : term

open Lean Elab Term in
private meta def manualThemePair [Monad m] [MonadRef m] [MonadQuotation m] (n : Name) : m Term := do
  let quoted : Term := quote n
  let ident ← mkCIdentFromRef n
  `(($quoted, $(⟨ident⟩)))

open Lean Elab Term in
/--
Elaborator for the {lit}`manual_themes%` macro: emits a
{name}`ManualThemeTable` literal whose entries are every registered
{name}`ManualTheme` decl.
-/
@[term_elab manual_themes]
meta def elabManualThemes : TermElab := fun _stx expected? => do
  let env ← getEnv
  let mut names : Array Name := #[]
  for n in manualThemeExt.getState env do
    names := names.push n
  for imported in manualThemeExt.toEnvExtension.getState env |>.importedEntries do
    for n in imported do
      names := names.push n
  let stx ← `(Verso.Theme.ManualThemeTable.fromList [$[($(← names.mapM manualThemePair) : Lean.Name × Verso.Theme.ManualTheme)],*])
  elabTerm stx expected?

end section

/-! # CSS variables -/

namespace ManualTheme

private def cssDecl (name value : String) : String :=
  s!"  --{name}: {value};\n"

private def colorDecl (name : String) (c : Color) : String :=
  cssDecl name (Color.css c)

/--
The CSS-variable body for the manual-chrome fields a {name}`ManualTheme` adds on top of
its inherited {name}`CodeTheme`. The manual genre concatenates this with
{name}`CodeTheme.cssVariables` to produce the contents of its
{lit}`:root` block.
-/
public def manualCssVariables (theme : ManualTheme) : String :=
  String.join [
    cssDecl "verso-text-font-family" theme.textFace.cssFamily,
    cssDecl "verso-structure-font-family" theme.structureFace.cssFamily,
    colorDecl "verso-surface-color" theme.surfaceColor,
    colorDecl "verso-header-background" theme.headerBackground,
    colorDecl "verso-toc-background-color" theme.tocBackground,
    colorDecl "verso-border-color" theme.borderColor,
    colorDecl "verso-muted-color" theme.mutedColor,
    colorDecl "verso-highlight-color" theme.highlightColor,
    colorDecl "verso-link-color" theme.linkColor,
    colorDecl "verso-visited-link-color" theme.visitedLinkColor,
    colorDecl "verso-toc-text-color" theme.tocTextColor,
    colorDecl "verso-burger-toc-visible-color" theme.burgerVisibleColor,
    colorDecl "verso-burger-toc-visible-shadow-color" theme.burgerVisibleShadowColor,
    colorDecl "verso-burger-toc-hidden-color" theme.burgerHiddenColor,
    colorDecl "verso-burger-toc-hidden-shadow-color" theme.burgerHiddenShadowColor
  ]

/--
The full CSS-variable body for a {name}`ManualTheme`: the inherited
{name}`CodeTheme` variables followed by the manual-chrome additions. This is
what the manual genre writes into the body of {lit}`verso-themes.css`'s {lit}`:root` block.
-/
public def cssVariables (theme : ManualTheme) : String :=
  theme.toCodeTheme.cssVariables ++ theme.manualCssVariables

end ManualTheme

/-! # Accessibility -/

namespace ManualTheme

/--
Runs the inherited {name}`CodeTheme.checkAccessibility` and then verifies the
manual-chrome pairs:

- content {name}`linkColor` and {name}`visitedLinkColor` against the page background
- {name}`tocTextColor` against the {name}`tocBackground`
- the header title color (body text) against {name}`headerBackground`
- the search-box muted and border colors against the surface and page backgrounds
- body text against the {name}`highlightColor`, since search results render matched terms with that
  color as their background
-/
public def checkAccessibility (theme : ManualTheme) : Array Color.Issue := Id.run do
  let mut issues := theme.toCodeTheme.checkAccessibility
  issues := issues ++ Color.contrastIssues Color.textContrastThreshold
    "link color on page background" theme.linkColor theme.background
  issues := issues ++ Color.contrastIssues Color.textContrastThreshold
    "visited link color on page background" theme.visitedLinkColor theme.background
  issues := issues ++ Color.contrastIssues Color.textContrastThreshold
    "toc text on toc background" theme.tocTextColor theme.tocBackground
  issues := issues ++ Color.contrastIssues Color.textContrastThreshold
    "header title on header background" theme.textColor theme.headerBackground
  issues := issues ++ Color.contrastIssues Color.textContrastThreshold
    "body text on highlight background" theme.textColor theme.highlightColor
  issues := issues ++ Color.contrastIssues Color.largeContrastThreshold
    "border color on surface" theme.borderColor theme.surfaceColor
  issues := issues ++ Color.contrastIssues Color.largeContrastThreshold
    "border color on page background" theme.borderColor theme.background
  -- "Muted text" is for incidental hints (search placeholder, secondary metadata) and so
  -- uses the AA Large / UI 3.0 threshold rather than 4.5 for primary body text.
  issues := issues ++ Color.contrastIssues Color.largeContrastThreshold
    "muted text on surface" theme.mutedColor theme.surfaceColor
  issues := issues ++ Color.contrastIssues Color.largeContrastThreshold
    "muted text on page background" theme.mutedColor theme.background
  return issues

end ManualTheme

/-! # Theme-set validation -/

namespace ManualThemeTable

/--
A theme's registration name is used as an identifier in {lit}`data-verso-theme`,
{lit}`localStorage`, and asset paths. Each character must satisfy {lit}`[A-Za-z0-9._-]`;
consecutive dots ({lit}`..`) are rejected to prevent path traversal in the asset directory; and
the slug must contain at least one letter so a bare {lit}`.` is rejected.
-/
public def safeNameString (s : String) : Bool := Id.run do
  if s.isEmpty then return false
  if (s.splitOn "..").length > 1 then return false
  let mut hasLetter := false
  for c in s.toList do
    if c.isAlpha then hasLetter := true
    let ok := c.isAlphanum || c == '.' || c == '-' || c == '_'
    unless ok do return false
  return hasLetter

/--
Reasons a theme configuration can be rejected. Each carries enough detail to point an author at
the specific theme or default slot that needs attention.
-/
public inductive ValidationError where
  /--
  The registration {name}`Name.toString` contains characters outside `[A-Za-z0-9._-]`, contains
  `..`, or has no letter.
  -/
  | unsafeName (name : Lean.Name)
  /-- The set of avaialable themes named a theme that is not registered with {attr}`@[manual_theme]`. -/
  | unknownAvailable (name : Lean.Name)
  /-- The default light theme is not a registered manual theme. -/
  | unknownDefaultLight (name : Lean.Name)
  /-- The default dark theme is not a registered manual theme. -/
  | unknownDefaultDark (name : Lean.Name)
  /-- The default light theme is a dark theme. -/
  | defaultLightWrongAppearance (name : Lean.Name)
  /-- The default dark theme is a light theme. -/
  | defaultDarkWrongAppearance (name : Lean.Name)
deriving Inhabited, Repr

/-- Renders a {name}`ValidationError` as a build-log message. -/
public def ValidationError.format : ValidationError → String
  | .unsafeName n =>
    s!"theme registration name '{n}' is not safe for a URL path segment; only [A-Za-z0-9._-] are allowed, '..' is rejected, and at least one letter is required"
  | .unknownAvailable n =>
    s!"availableThemes lists '{n}', which is not a registered @[manual_theme]"
  | .unknownDefaultLight n =>
    s!"defaultLightTheme = '{n}' is not a registered @[manual_theme]"
  | .unknownDefaultDark n =>
    s!"defaultDarkTheme = '{n}' is not a registered @[manual_theme]"
  | .defaultLightWrongAppearance n =>
    s!"defaultLightTheme = '{n}' is registered but its appearance is not .light"
  | .defaultDarkWrongAppearance n =>
    s!"defaultDarkTheme = '{n}' is registered but its appearance is not .dark"

open Lean in
/--
Validates the configured theme set against the registered theme table. Returns the list of
problems found (empty iff every check passes); the caller routes them through the build log.
-/
public def validate (table : ManualThemeTable)
    (defaultLight defaultDark : Name)
    (available : Option NameSet) : Array ValidationError := Id.run do
  let mut errs := #[]
  for (n, _) in table.themes.toList do
    unless safeNameString n.toString do
      errs := errs.push (.unsafeName n)
  if let some xs := available then
    for n in xs do
      unless (table.find? n).isSome do
        errs := errs.push (.unknownAvailable n)
  match table.find? defaultLight with
  | none => errs := errs.push (.unknownDefaultLight defaultLight)
  | some t => unless t.appearance == .light do
      errs := errs.push (.defaultLightWrongAppearance defaultLight)
  match table.find? defaultDark with
  | none => errs := errs.push (.unknownDefaultDark defaultDark)
  | some t => unless t.appearance == .dark do
      errs := errs.push (.defaultDarkWrongAppearance defaultDark)
  return errs
