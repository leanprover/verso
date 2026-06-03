/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public meta import Verso.Theme.Code.Ext
public import Verso.Theme.Color
public import Verso.Theme.Color.Accessibility
public import Verso.Theme.SourceLink
public import Verso.Font
public meta import Lean.Elab.Term

set_option linter.missingDocs true
set_option doc.verso true

/-!
The genre-neutral code theme: a typed set of colors, token styles, and font choices that the
manual genre uses to render code blocks and inline code. Default values reproduce today's
hardcoded chrome.
-/

namespace Verso.Theme

/-- Whether a theme is intended for a light or a dark display. -/
public inductive Appearance where
  | light
  | dark
deriving DecidableEq, Repr

/-- Styling for a single token kind: its color, weight, font style, and the face it uses. -/
public structure TokenStyle where
  /-- The token's text color. -/
  color : Color
  /-- The token's font weight (CSS 1–1000). -/
  weight : Weight := .regular
  /-- The token's font style (upright or italic). -/
  style : FontStyle := .normal
  /-- The font used for this token. -/
  face : Typeface

/-- A bundled asset (such as an image) shipped with a theme. -/
public structure ThemeAsset where
  /-- The output-relative path the asset will be written to. -/
  path : String
  /-- The asset bytes, embedded at compile time. -/
  contents : ByteArray

/--
A typed code theme. Defaults reproduce today's hardcoded chrome, so a default-constructed theme is
visually unchanged from the pre-theming look.

Many field defaults refer to earlier fields (for example a token color defaults to
{lit}`codeColor`, which in turn defaults to {lit}`textColor`). Lean evaluates defaults at
the moment a theme value is constructed, so on a fresh construction overriding a referenced
field propagates to every later field that defaulted from it. A {lit}`with` update against
an *existing* theme value freezes the defaults that were already computed there, so a
substantially different theme (a dark variant of a light base, say) needs to set the
dependent fields explicitly.
-/
public structure CodeTheme where
  /-- A human-readable name for the theme (shown in the picker). -/
  name : String
  /-- Whether this theme is intended for a light or a dark display. -/
  appearance : Appearance
  /--
  An optional one- or two-sentence description shown alongside the theme in the picker. Useful
  for noting design intent, palette family, or accessibility trade-offs.
  -/
  description : Option String := none
  /--
  An optional canonical reference for the theme: a URL plus link text shown next to the name
  in the picker. Points readers at an upstream homepage or specification when the theme is a
  port.
  -/
  sourceLink : Option SourceLink := none

  /-- The font used for code blocks and inline code. -/
  codeFace : Typeface := .mono

  /-- The page and content background color. The contrast reference for body text. -/
  background : Color
  /-- The background behind code blocks. The contrast reference for token colors. -/
  codeBlockBackground : Color := background
  /-- The background behind inline code in prose. When set, inline code gets padding and rounding. -/
  inlineBackground : Option Color := none
  /-- The color of body prose text. -/
  textColor : Color
  /-- The color of code text. -/
  codeColor : Color := textColor
  /-- The color used for structural decoration (such as case labels). -/
  structureColor : Color := textColor
  /-- The background color used to highlight a selected token in code. -/
  selectedColor : Color

  /-- The message-text color for informational diagnostics. -/
  infoColor : Color := textColor
  /-- The accent color (left border, underline) for informational diagnostics. -/
  infoIndicatorColor : Color
  /-- The message-text color for warning diagnostics. -/
  warningColor : Color := textColor
  /-- The accent color (left border, underline) for warning diagnostics. -/
  warningIndicatorColor : Color
  /-- The message-text color for error diagnostics. -/
  errorColor : Color
  /-- The accent color (left border, underline) for error diagnostics. -/
  errorIndicatorColor : Color

  /-- Token styling for constants. -/
  const : TokenStyle := { color := codeColor, weight := .regular, style := .normal, face := codeFace }
  /-- Token styling for keywords. -/
  keyword : TokenStyle := { color := codeColor, weight := .bold, style := .normal, face := codeFace }
  /-- Token styling for variables (bound names). -/
  «var» : TokenStyle := { color := codeColor, weight := .regular, style := .italic, face := codeFace }
  /--
  Token styling for literal tokens.
  -/
  literal : TokenStyle := { color := codeColor, weight := .regular, style := .normal, face := codeFace }
  /--
  Token styling for string literals.
  -/
  literalString : TokenStyle := literal
  /--
  Token styling for numeric literals.
  -/
  literalNumber : TokenStyle := literal
  /--
  Token styling for character literals.
  -/
  literalChar : TokenStyle := literalString
  /--
  Token styling for docstrings.
  -/
  docComment : TokenStyle := { color := codeColor, weight := .regular, style := .italic, face := codeFace }
  /--
  Token styling for the body text of ordinary comments, both {lit}`--` line comments and
  {lit}`/- … -/` block comments.
  -/
  comment : TokenStyle := { color := codeColor, weight := .regular, style := .normal, face := codeFace }
  /--
  Token styling for comment delimiters — the {lit}`--` opener of a line comment and the
  {lit}`/-`/{lit}`-/` openers/closers of a block comment.
  -/
  commentDelim : TokenStyle := comment
  /--
  Token styling for sort formers: {lit}`Type`, {lit}`Prop`, {lit}`Sort`.
  -/
  sort : TokenStyle := { color := codeColor, weight := .regular, style := .normal, face := codeFace }
  /--
  Token styling for universe-level variables ({lit}`u`, {lit}`v`, … in a universe-parameter
  context).
  -/
  levelVar : TokenStyle := { color := codeColor, weight := .regular, style := .italic, face := codeFace }
  /--
  Token styling for universe-level numeric constants (the {lit}`3` in {lit}`Type 3`).
  -/
  levelConst : TokenStyle := { color := codeColor, weight := .regular, style := .normal, face := codeFace }
  /--
  Token styling for universe-level operators ({lit}`max`, {lit}`imax`, {lit}`+`).
  -/
  levelOp : TokenStyle := { color := codeColor, weight := .regular, style := .normal, face := codeFace }
  /--
  Token styling for module names (e.g. an {lit}`import` target).
  -/
  moduleName : TokenStyle := { color := codeColor, weight := .regular, style := .normal, face := codeFace }
  /--
  Token styling for built-in syntactic delimiters such as {lit}`:=`, {lit}`=>`, {lit}`←`, {lit}`@`,
  {lit}`:`, {lit}`|`. CSS class {lit}`.delim`.
  -/
  delim : TokenStyle := { color := codeColor, weight := .regular, style := .normal, face := codeFace }
  /--
  Token styling for symbolic operator atoms such as {lit}`+`, {lit}`::`, {lit}`>>=`. CSS class
  {lit}`.punctuation.operator`.
  -/
  operator : TokenStyle := delim
  /--
  Token styling for paired delimiter atoms such as {lit}`(` {lit}`)`, {lit}`[` {lit}`]`, {lit}`{`
  {lit}`}`, {lit}`⟨`, {lit}`⟩`.
  -/
  bracket : TokenStyle := delim
  /--
  Token styling for item-separator atoms such as {lit}`,` and {lit}`;`.
  -/
  separator : TokenStyle := delim

  /-- The background of hover popups, diagnostic boxes, and tooltips. -/
  hoverBackground : Color
  /-- The border color of hover popups and plain tooltips. -/
  hoverBorderColor : Color
  /-- The text color inside hover popups. -/
  hoverText : Color := textColor
  /-- The separator line color inside hover popups. -/
  hoverSeparatorColor : Color
  /-- The background tint applied to a token on hover (independent of severity). -/
  tokenHighlightBackground : Color
  /--
  The background of a displayed tactic state.
  -/
  tacticStateBackground : Color := codeBlockBackground
  /-- The border color of a displayed tactic state. -/
  tacticStateBorderColor : Color

  /--
  An accent background drawn behind highlighted code.
  {name (full := CodeTheme.codeColor)}`codeColor` must read on it.
  -/
  highlightOnCode : Color
  /-- An accent background drawn behind highlighted code or prose. Both code and text must read on it. -/
  highlightOnText : Color := highlightOnCode
  /--
  A neutral UI element color drawn against
  {name (full := CodeTheme.codeBlockBackground)}`codeBlockBackground` (e.g. a toggle pill).
  -/
  uiOnCode : Color

  /--
  Theme-specific CSS appended after the standard variable block. The asset root path the function
  receives is relative to {lit}`verso-themes.css` so {lit}`url()` references resolve from there.
  -/
  extraCss : (assetRoot : String) → String := fun _ => ""
  /-- Non-font assets (such as images) bundled with the theme. -/
  assets : Array ThemeAsset := #[]

/-! # Attribute, environment extension, and materialization -/

public section

/--
Attribute that registers a {name}`CodeTheme` declaration as an available theme. The
declaration must be in the current module (not imported), and its registration name is the decl's
name with macro scopes erased.
-/
syntax (name := code_theme) "code_theme" : attr

open Lean in
meta initialize
  registerBuiltinAttribute {
    name := `code_theme,
    ref := by exact decl_name%,
    add := fun decl _stx kind => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'code_theme', must be global"
      unless ((← getEnv).getModuleIdxFor? decl).isNone do
        throwError "invalid attribute 'code_theme', declaration is in an imported module"
      modifyEnv fun env => codeThemeExt.addEntry env decl.eraseMacroScopes
    descr := "Registers a definition as an available code theme"
  }

end section

/--
A materialized table of registered {name}`CodeTheme` values, keyed by registration name.
Built at runtime by the {lit}`code_themes%` term elaborator from the set of
{name}`CodeTheme` declarations tagged with the {lit}`@[code_theme]` attribute.
-/
public structure CodeThemeTable where
  /-- The map from a theme's registration name to its value. -/
  themes : Lean.NameMap CodeTheme := {}

namespace CodeThemeTable

/-- The empty table. -/
public def empty : CodeThemeTable := {}

public instance : EmptyCollection CodeThemeTable := ⟨empty⟩

/-- Looks up a theme by its registration name. -/
public def find? (t : CodeThemeTable) (n : Lean.Name) : Option CodeTheme :=
  t.themes.find? n

/-- Inserts a theme under the given registration name. -/
public def insert (t : CodeThemeTable) (n : Lean.Name) (theme : CodeTheme) : CodeThemeTable :=
  ⟨t.themes.insert n theme⟩

/-- Builds a table from a list of pairs. -/
public def fromList (xs : List (Lean.Name × CodeTheme)) : CodeThemeTable :=
  xs.foldl (fun (acc : CodeThemeTable) (p : Lean.Name × CodeTheme) => acc.insert p.1 p.2) empty

end CodeThemeTable

public section

/-- Term elaborator that materializes the registered code-theme table at compile time. -/
syntax (name := code_themes) "code_themes%" : term

open Lean Elab Term in
private meta def themePair [Monad m] [MonadRef m] [MonadQuotation m] (n : Name) : m Term := do
  let quoted : Term := quote n
  let ident ← mkCIdentFromRef n
  `(($quoted, $(⟨ident⟩)))

open Lean Elab Term in
/--
Elaborator for the {lit}`code_themes%` macro: emits a {name}`CodeThemeTable`
literal whose entries are every registered {name}`CodeTheme` decl.
-/
@[term_elab code_themes]
meta def elabCodeThemes : TermElab := fun _stx expected? => do
  let env ← getEnv
  let mut names : Array Name := #[]
  for n in codeThemeExt.getState env do
    names := names.push n
  for imported in codeThemeExt.toEnvExtension.getState env |>.importedEntries do
    for n in imported do
      names := names.push n
  let stx ← `(Verso.Theme.CodeThemeTable.fromList [$[($(← names.mapM themePair) : Lean.Name × Verso.Theme.CodeTheme)],*])
  elabTerm stx expected?

end section

/-! # Accessibility checking -/

namespace CodeTheme

/-- The display name and color of a token style, for accessibility reporting. -/
private def tokenSummaries (theme : CodeTheme) : Array (String × Color) := #[
    ("const", theme.const.color),
    ("keyword", theme.keyword.color),
    ("var", theme.«var».color),
    ("literal", theme.literal.color),
    ("literal.string", theme.literalString.color),
    ("literal.number", theme.literalNumber.color),
    ("literal.char", theme.literalChar.color),
    ("doc-comment", theme.docComment.color),
    ("comment", theme.comment.color),
    ("comment.delimiter", theme.commentDelim.color),
    ("sort", theme.sort.color),
    ("level-var", theme.levelVar.color),
    ("level-const", theme.levelConst.color),
    ("level-op", theme.levelOp.color),
    ("module-name", theme.moduleName.color),
    ("delim", theme.delim.color),
    ("punctuation.operator", theme.operator.color),
    ("punctuation.bracket", theme.bracket.color),
    ("punctuation.separator", theme.separator.color)
  ]

/--
{open Verso.Theme.Color}

Checks a theme for contrast and color-vision-deficiency problems. The checker is pure and genre
neutral: it returns an {Lean.Doc.name}`Array` of {Lean.Doc.name}`Issue` values
whose {Lean.Doc.name}`Issue.kind` field a caller routes to its severity flag.

Body text uses the WCAG AA 4.5 threshold; UI accents and large-text positions use 3.0. Token
distinguishability uses the CIEDE2000 threshold from
{Lean.Doc.name}`distinguishableThreshold`.
-/
public def checkAccessibility (theme : CodeTheme) : Array Color.Issue := Id.run do
  let mut issues := #[]
  -- Body and message text on the page background.
  issues := issues ++ Color.contrastIssues Color.textContrastThreshold
    "body text on background" theme.textColor theme.background
  issues := issues ++ Color.contrastIssues Color.textContrastThreshold
    "error message text on background" theme.errorColor theme.background
  issues := issues ++ Color.contrastIssues Color.textContrastThreshold
    "warning message text on background" theme.warningColor theme.background
  issues := issues ++ Color.contrastIssues Color.textContrastThreshold
    "info message text on background" theme.infoColor theme.background
  -- Code tokens against the code-block background.
  for (n, c) in theme.tokenSummaries do
    issues := issues ++ Color.contrastIssues Color.textContrastThreshold
      s!"{n} token on code background" c theme.codeBlockBackground
  -- Inline-code background, when set, must read with the code color.
  if let some bg := theme.inlineBackground then
    issues := issues ++ Color.contrastIssues Color.textContrastThreshold
      "code on inline background" theme.codeColor bg
  -- Indicator accents against the page background.
  issues := issues ++ Color.contrastIssues Color.largeContrastThreshold
    "error indicator on background" theme.errorIndicatorColor theme.background
  issues := issues ++ Color.contrastIssues Color.largeContrastThreshold
    "warning indicator on background" theme.warningIndicatorColor theme.background
  issues := issues ++ Color.contrastIssues Color.largeContrastThreshold
    "info indicator on background" theme.infoIndicatorColor theme.background
  -- Highlight backgrounds.
  issues := issues ++ Color.contrastIssues Color.textContrastThreshold
    "code on highlightOnCode" theme.codeColor theme.highlightOnCode
  issues := issues ++ Color.contrastIssues Color.textContrastThreshold
    "code on highlightOnText" theme.codeColor theme.highlightOnText
  issues := issues ++ Color.contrastIssues Color.textContrastThreshold
    "text on highlightOnText" theme.textColor theme.highlightOnText
  -- UI element on code background (large/UI threshold).
  issues := issues ++ Color.contrastIssues Color.largeContrastThreshold
    "uiOnCode against code background" theme.uiOnCode theme.codeBlockBackground
  -- Tactic state border on its background.
  issues := issues ++ Color.contrastIssues Color.largeContrastThreshold
    "tactic-state border on its background"
    theme.tacticStateBorderColor theme.tacticStateBackground
  -- Hover popup readability.
  issues := issues ++ Color.contrastIssues Color.textContrastThreshold
    "hover-popup text on hover background" theme.hoverText theme.hoverBackground
  -- Tactic popups draw the same hover text on the tactic-state background.
  issues := issues ++ Color.contrastIssues Color.textContrastThreshold
    "hover-popup text on tactic-state background"
    theme.hoverText theme.tacticStateBackground
  -- Code drawn on the tactic-state background (for example a hypothesis).
  issues := issues ++ Color.contrastIssues Color.textContrastThreshold
    "code on tactic-state background" theme.codeColor theme.tacticStateBackground
  -- Colorblindness: token colors stay mutually distinguishable. Severity indicators are
  -- intentionally excluded here: error red and warning yellow/amber routinely collapse under
  -- protanopia and deuteranopia, but they are visually paired with their distinct semantics
  -- (text content, icons) so the color collision is not the only signal.
  issues := issues ++ Color.colorblindIssues Color.distinguishableThreshold theme.tokenSummaries
  return issues

end CodeTheme

/-! # CSS variable block -/

namespace CodeTheme

/-- Renders a single `--name: value;` CSS declaration. -/
private def cssDecl (name value : String) : String :=
  s!"  --{name}: {value};\n"

private def colorDecl (name : String) (c : Color) : String :=
  cssDecl name (Color.css c)

private def styleDecls (prefix' : String) (s : TokenStyle) : String :=
  String.join [
    colorDecl s!"{prefix'}-color" s.color,
    cssDecl s!"{prefix'}-weight" (toString s.weight.val),
    cssDecl s!"{prefix'}-style" (match s.style with | .normal => "normal" | .italic => "italic"),
    cssDecl s!"{prefix'}-font-family" s.face.cssFamily
  ]

/--
Renders the theme as the body of a CSS `:root { ... }` block: one `--verso-*` custom property per
themed value. The output drives the page-level theme stylesheet and replaces the resolved values
that today are hardcoded into {lit}`verso-vars.css` and {lit}`highlightingStyle`.
-/
public def cssVariables (theme : CodeTheme) : String :=
  String.join [
    colorDecl "verso-background-color" theme.background,
    colorDecl "verso-code-background-color" theme.codeBlockBackground,
    (match theme.inlineBackground with
     | some c => colorDecl "verso-inline-code-background-color" c
     | none => ""),
    colorDecl "verso-text-color" theme.textColor,
    colorDecl "verso-code-color" theme.codeColor,
    colorDecl "verso-structure-color" theme.structureColor,
    colorDecl "verso-selected-color" theme.selectedColor,
    colorDecl "verso-info-color" theme.infoColor,
    colorDecl "verso-info-indicator-color" theme.infoIndicatorColor,
    colorDecl "verso-warning-color" theme.warningColor,
    colorDecl "verso-warning-indicator-color" theme.warningIndicatorColor,
    colorDecl "verso-error-color" theme.errorColor,
    colorDecl "verso-error-indicator-color" theme.errorIndicatorColor,
    cssDecl "verso-code-font-family" theme.codeFace.cssFamily,
    styleDecls "verso-code-const" theme.const,
    styleDecls "verso-code-keyword" theme.keyword,
    styleDecls "verso-code-var" theme.«var»,
    styleDecls "verso-code-literal" theme.literal,
    styleDecls "verso-code-literal-string" theme.literalString,
    styleDecls "verso-code-literal-number" theme.literalNumber,
    styleDecls "verso-code-literal-char" theme.literalChar,
    styleDecls "verso-code-doc-comment" theme.docComment,
    styleDecls "verso-code-comment" theme.comment,
    styleDecls "verso-code-comment-delim" theme.commentDelim,
    styleDecls "verso-code-sort" theme.sort,
    styleDecls "verso-code-level-var" theme.levelVar,
    styleDecls "verso-code-level-const" theme.levelConst,
    styleDecls "verso-code-level-op" theme.levelOp,
    styleDecls "verso-code-module-name" theme.moduleName,
    styleDecls "verso-code-delim" theme.delim,
    styleDecls "verso-code-operator" theme.operator,
    styleDecls "verso-code-bracket" theme.bracket,
    styleDecls "verso-code-separator" theme.separator,
    colorDecl "verso-hover-background-color" theme.hoverBackground,
    colorDecl "verso-hover-border-color" theme.hoverBorderColor,
    colorDecl "verso-hover-text-color" theme.hoverText,
    colorDecl "verso-hover-separator-color" theme.hoverSeparatorColor,
    colorDecl "verso-token-highlight-background-color" theme.tokenHighlightBackground,
    colorDecl "verso-tactic-state-background-color" theme.tacticStateBackground,
    colorDecl "verso-tactic-state-border-color" theme.tacticStateBorderColor,
    colorDecl "verso-highlight-on-code-color" theme.highlightOnCode,
    colorDecl "verso-highlight-on-text-color" theme.highlightOnText,
    colorDecl "verso-ui-on-code-color" theme.uiOnCode
  ]

end CodeTheme

/-! # TeX preamble -/

namespace CodeTheme

private def fontSeries (w : Weight) : String :=
  -- The NFSS series codes that are widely supported by fontspec/luaotfload. We map the requested
  -- numeric weight to the nearest standard series; LuaLaTeX uses the series to pick a face. A
  -- finer mapping is unnecessary because the variable/extra weights are handled by the font
  -- loader, not by `\fontseries`.
  let v := w.val
  if v ≤ 200 then "ul"
  else if v ≤ 300 then "el"
  else if v ≤ 350 then "l"
  else if v ≤ 450 then "m"
  else if v ≤ 550 then "sb"
  else if v ≤ 650 then "b"
  else if v ≤ 750 then "eb"
  else "ub"

private def fontShape : FontStyle → String
  | .normal => "n"
  | .italic => "it"

private def tokenMacro (name : String) (s : TokenStyle) (colorName : String) : String :=
  s!"\\renewcommand\{\\verso{name}}[1]\{\\textcolor\{{colorName}}\{\\fontseries\{{fontSeries s.weight}}\\fontshape\{{fontShape s.style}}\\selectfont #1}}\n"

/--
Returns a TeX preamble fragment that defines a theme-specific {lit}`xcolor` palette, redefines
the four {lit}`\verso…` token macros so they apply the theme's per-token color, weight, and
style, and sets the document mono font to {Lean.Doc.name (full := Typeface.texFamily)}`texFamily` applied to
{Lean.Doc.name}`codeFace`.

Two color names are emitted per severity: {lit}`errorColor`/{lit}`warningColor`/{lit}`infoColor`
are the message-text colors, and {lit}`errorIndicatorColor`/{lit}`warningIndicatorColor`/{lit}`infoIndicatorColor`
are the accent colors used for the wavy underlines and frames. The output is intended to be
appended after Verso's manual preamble (which carries the {lit}`\providecommand` fallbacks for
the {lit}`\verso…` macros). It uses {lit}`xcolor`'s {lit}`HTML` model and NFSS series/shape
codes that fontspec understands under LuaLaTeX.
-/
public def texPreamble (theme : CodeTheme) : String :=
  let codeColor := Color.tex theme.codeColor
  let constColor := Color.tex theme.const.color
  let keywordColor := Color.tex theme.keyword.color
  let varColor := Color.tex theme.«var».color
  let literalColor := Color.tex theme.literal.color
  let literalStringColor := Color.tex theme.literalString.color
  let literalNumberColor := Color.tex theme.literalNumber.color
  let literalCharColor := Color.tex theme.literalChar.color
  let docCommentColor := Color.tex theme.docComment.color
  let commentColor := Color.tex theme.comment.color
  let commentDelimColor := Color.tex theme.commentDelim.color
  let sortColor := Color.tex theme.sort.color
  let levelVarColor := Color.tex theme.levelVar.color
  let levelConstColor := Color.tex theme.levelConst.color
  let levelOpColor := Color.tex theme.levelOp.color
  let moduleNameColor := Color.tex theme.moduleName.color
  let delimColor := Color.tex theme.delim.color
  let operatorColor := Color.tex theme.operator.color
  let bracketColor := Color.tex theme.bracket.color
  let separatorColor := Color.tex theme.separator.color
  -- Per the structure's semantics, the `*Color` fields are message-text colors and
  -- `*IndicatorColor` are accent colors (underlines, frames, dingbats). Emit both as separate
  -- `\definecolor` entries so the preamble can reference whichever the rule needs.
  let errorTextColor := Color.tex theme.errorColor
  let warningTextColor := Color.tex theme.warningColor
  let infoTextColor := Color.tex theme.infoColor
  let errorAccent := Color.tex theme.errorIndicatorColor
  let warningAccent := Color.tex theme.warningIndicatorColor
  let infoAccent := Color.tex theme.infoIndicatorColor
  String.join [
    s!"\\definecolor\{versoCodeColor}\{HTML}\{{codeColor}}\n",
    s!"\\definecolor\{versoConstColor}\{HTML}\{{constColor}}\n",
    s!"\\definecolor\{versoKeywordColor}\{HTML}\{{keywordColor}}\n",
    s!"\\definecolor\{versoVarColor}\{HTML}\{{varColor}}\n",
    s!"\\definecolor\{versoLiteralColor}\{HTML}\{{literalColor}}\n",
    s!"\\definecolor\{versoLiteralStringColor}\{HTML}\{{literalStringColor}}\n",
    s!"\\definecolor\{versoLiteralNumberColor}\{HTML}\{{literalNumberColor}}\n",
    s!"\\definecolor\{versoLiteralCharColor}\{HTML}\{{literalCharColor}}\n",
    s!"\\definecolor\{versoDocCommentColor}\{HTML}\{{docCommentColor}}\n",
    s!"\\definecolor\{versoCommentColor}\{HTML}\{{commentColor}}\n",
    s!"\\definecolor\{versoCommentDelimColor}\{HTML}\{{commentDelimColor}}\n",
    s!"\\definecolor\{versoSortColor}\{HTML}\{{sortColor}}\n",
    s!"\\definecolor\{versoLevelVarColor}\{HTML}\{{levelVarColor}}\n",
    s!"\\definecolor\{versoLevelConstColor}\{HTML}\{{levelConstColor}}\n",
    s!"\\definecolor\{versoLevelOpColor}\{HTML}\{{levelOpColor}}\n",
    s!"\\definecolor\{versoModuleNameColor}\{HTML}\{{moduleNameColor}}\n",
    s!"\\definecolor\{versoDelimColor}\{HTML}\{{delimColor}}\n",
    s!"\\definecolor\{versoOperatorColor}\{HTML}\{{operatorColor}}\n",
    s!"\\definecolor\{versoBracketColor}\{HTML}\{{bracketColor}}\n",
    s!"\\definecolor\{versoSeparatorColor}\{HTML}\{{separatorColor}}\n",
    s!"\\definecolor\{errorColor}\{HTML}\{{errorTextColor}}\n",
    s!"\\definecolor\{warningColor}\{HTML}\{{warningTextColor}}\n",
    s!"\\definecolor\{infoColor}\{HTML}\{{infoTextColor}}\n",
    s!"\\definecolor\{errorIndicatorColor}\{HTML}\{{errorAccent}}\n",
    s!"\\definecolor\{warningIndicatorColor}\{HTML}\{{warningAccent}}\n",
    s!"\\definecolor\{infoIndicatorColor}\{HTML}\{{infoAccent}}\n",
    tokenMacro "Keyword" theme.keyword "versoKeywordColor",
    tokenMacro "Const" theme.const "versoConstColor",
    tokenMacro "Var" theme.«var» "versoVarColor",
    tokenMacro "Literal" theme.literal "versoLiteralColor",
    tokenMacro "LiteralString" theme.literalString "versoLiteralStringColor",
    tokenMacro "LiteralNumber" theme.literalNumber "versoLiteralNumberColor",
    tokenMacro "LiteralChar" theme.literalChar "versoLiteralCharColor",
    tokenMacro "DocComment" theme.docComment "versoDocCommentColor",
    tokenMacro "Comment" theme.comment "versoCommentColor",
    tokenMacro "CommentDelim" theme.commentDelim "versoCommentDelimColor",
    tokenMacro "Sort" theme.sort "versoSortColor",
    tokenMacro "LevelVar" theme.levelVar "versoLevelVarColor",
    tokenMacro "LevelConst" theme.levelConst "versoLevelConstColor",
    tokenMacro "LevelOp" theme.levelOp "versoLevelOpColor",
    tokenMacro "ModuleName" theme.moduleName "versoModuleNameColor",
    tokenMacro "Delim" theme.delim "versoDelimColor",
    tokenMacro "Operator" theme.operator "versoOperatorColor",
    tokenMacro "Bracket" theme.bracket "versoBracketColor",
    tokenMacro "Separator" theme.separator "versoSeparatorColor",
    s!"\\setmonofont\{{theme.codeFace.texFamily}}\n"
  ]

end CodeTheme

/-! # Font assets and {lit}`@font-face` writing -/

namespace CodeTheme

/--
Every {Lean.Doc.name}`Typeface` referenced by a theme. Built-in
{Lean.Doc.name (full := Typeface.sans)}`sans`/{Lean.Doc.name (full := Typeface.serif)}`serif`/{Lean.Doc.name (full := Typeface.mono)}`mono`
are skipped: only {Lean.Doc.name (full := Typeface.files)}`files` typefaces contribute font assets.
-/
public def fileTypefaces (theme : CodeTheme) : Array Typeface :=
  let faces := #[theme.codeFace, theme.const.face, theme.keyword.face, theme.«var».face,
    theme.delim.face, theme.operator.face, theme.bracket.face, theme.separator.face]
  faces.filter fun
    | .files _ _ => true
    | _ => false

/-- The output file extension for a font format. -/
public def _root_.Verso.FontFormat.ext : FontFormat → String
  | .woff2 => "woff2"
  | .woff => "woff"
  | .otf => "otf"
  | .ttf => "ttf"

/--
Sanitizes a font-family name into a path-safe slug. Letters, digits, hyphens, underscores, and
dots are preserved; every other character becomes a hyphen, runs of hyphens collapse, and the
result is trimmed of leading/trailing hyphens. An empty result falls back to {lit}`font`.
-/
public def slugFamily (family : String) : String := Id.run do
  let mut buf := ""
  let mut prevHyphen := true
  for c in family.toList do
    let safe := c.isAlphanum || c == '-' || c == '_' || c == '.'
    if safe then
      buf := buf.push c
      prevHyphen := false
    else if !prevHyphen then
      buf := buf.push '-'
      prevHyphen := true
  let mut s := buf
  while s.endsWith "-" do s := (String.dropEnd s 1).copy
  if s.isEmpty then s := "font"
  return s

/--
Output-relative paths and bytes of every font file the theme uses. Each file is named
{lit}`<slug>-<typeface>-<face>.<ext>`, where {lit}`<slug>` is
{Lean.Doc.name}`slugFamily` applied to the family and {lit}`<typeface>` is
the index of the typeface within the theme's {Lean.Doc.name}`fileTypefaces`
array. The typeface index keeps paths distinct even when two families slug to the same string
(such as {lit}`"A B"` and {lit}`"A/B"` both becoming {lit}`A-B`). The {lit}`assetRoot` is the
directory the paths are relative to (no leading or trailing slash); the generated
{lit}`@font-face` {lit}`url()`s also resolve from there.
-/
public def fontAssets (theme : CodeTheme) (assetRoot : String) :
    Array (String × ByteArray × FontFace × String) := Id.run do
  let mut out := #[]
  for (tf, ti) in theme.fileTypefaces.zipIdx do
    if let .files family faces := tf then
      let slug := slugFamily family
      for (face, i) in faces.zipIdx do
        let path := s!"{assetRoot}/fonts/{slug}-{ti}-{i}.{face.format.ext}"
        out := out.push (path, face.bytes, face, family)
  return out

private def weightDecl : FaceWeights → String
  | .fixed w => toString w.val
  | .variable lo hi _ => s!"{lo.val} {hi.val}"

private def styleString : FontStyle → String
  | .normal => "normal"
  | .italic => "italic"

/--
The {lit}`@font-face` rules for every {Lean.Doc.name (full := Typeface.files)}`files`
typeface the theme uses. The {lit}`url()` paths are relative, so the rules resolve from whatever
stylesheet they end up in (in the manual genre, {lit}`verso-themes.css` at the site root).
-/
public def fontFaceRules (theme : CodeTheme) (assetRoot : String) : String := Id.run do
  let mut out := ""
  for (path, _bytes, face, family) in theme.fontAssets assetRoot do
    out := out ++ s!"@font-face \{\n"
    out := out ++ s!"  font-family: {cssQuote family};\n"
    out := out ++ s!"  font-weight: {weightDecl face.weights};\n"
    out := out ++ s!"  font-style: {styleString face.style};\n"
    out := out ++ s!"  src: url({cssQuote path}) format({cssQuote face.format.css});\n"
    out := out ++ "}\n"
  return out

end CodeTheme
