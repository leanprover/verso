/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/
module
meta import all Verso.Code.HighlightedToTex
public import Verso.Theme.Code
public import Verso.Theme.Code.Defaults
public import Verso.Font
meta import all Verso.Theme.Code
meta import all Verso.Theme.Code.Defaults
open Verso.Doc.TeX (escapeForVerbatim)

open SubVerso.Highlighting

/-- info: "\\symbol{123}\\symbol{124}\\symbol{125}\\symbol{92}" -/
#guard_msgs in
#eval escapeForVerbatim "{|}\\"

/-! Token rendering wraps each semantic category in a `\verso…` macro. The four categories cover
keywords, constants (including anonymous constructors and options), variables, and a catch-all
literal bucket. -/

/-- info: "\\versoKeyword{def}" -/
#guard_msgs in #eval (highlightToken "def" (.keyword none none "")).asString

/-- info: "\\versoConst{foo}" -/
#guard_msgs in #eval (highlightToken "foo" (.const `foo "" none false none)).asString

/-- info: "\\versoVar{x}" -/
#guard_msgs in #eval (highlightToken "x" (.var ⟨`x⟩ "" none)).asString

/-- info: "\\versoLiteral{42}" -/
#guard_msgs in #eval (highlightToken "42" .unknown).asString

/-! The fallback macro block defines the four `\verso…` macros with `\providecommand`, so a
preamble that defines its own (theme-driven) versions wins without an explicit `\renewcommand`. -/

/--
info: "\\providecommand{\\versoKeyword}[1]{\\textbf{#1}}\n\\providecommand{\\versoConst}[1]{#1}\n\\providecommand{\\versoVar}[1]{\\textit{#1}}\n\\providecommand{\\versoLiteral}[1]{#1}\n\\providecommand{\\versoLiteralString}[1]{#1}\n\\providecommand{\\versoDocComment}[1]{\\textit{#1}}\n\\providecommand{\\versoSort}[1]{#1}\n\\providecommand{\\versoLevelVar}[1]{\\textit{#1}}\n\\providecommand{\\versoLevelConst}[1]{#1}\n\\providecommand{\\versoLevelOp}[1]{#1}\n\\providecommand{\\versoModuleName}[1]{#1}\n\\providecommand{\\versoDelim}[1]{#1}\n\\providecommand{\\versoOperator}[1]{#1}\n\\providecommand{\\versoBracket}[1]{#1}\n\\providecommand{\\versoSeparator}[1]{#1}\n"
-/
#guard_msgs in #eval texMacroFallbacks

/-! The default code theme emits `\definecolor` blocks for its token and severity colors and
redefines each `\verso…` macro to apply the resolved color, weight, and style. -/

private def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- info: true -/
#guard_msgs in
#eval
  let p := Verso.Theme.CodeTheme.ink.texPreamble
  -- Message-text and accent colors are emitted under distinct names: `errorColor` is the
  -- message-body color (#cc0000 by default), `errorIndicatorColor` is the wavy-underline
  -- accent (#ff0000). The keyword macro picks up bold (NFSS `eb`), and the mono font is
  -- the bundled DejaVu Sans Mono.
  hasSub p "\\definecolor{errorColor}{HTML}{CC0000}" &&
  hasSub p "\\definecolor{errorIndicatorColor}{HTML}{FF0000}" &&
  hasSub p "\\renewcommand{\\versoKeyword}[1]{\\textcolor{versoKeywordColor}{\\fontseries{eb}\\fontshape{n}\\selectfont #1}}" &&
  hasSub p "\\setmonofont{DejaVu Sans Mono}"

/-! A deliberately colorful theme really does color and style the keyword and const tokens. -/

open Verso Verso.Theme in
private def colorfulTheme : CodeTheme := {
  CodeTheme.ink with
  keyword := { color := color%#aa3300, weight := 600, style := .normal, face := .mono },
  const := { color := color%#0044bb, weight := .regular, style := .italic, face := .mono }
}

/-- info: true -/
#guard_msgs in
#eval
  let p := colorfulTheme.texPreamble
  hasSub p "\\definecolor{versoKeywordColor}{HTML}{AA3300}" &&
  hasSub p "\\renewcommand{\\versoKeyword}[1]{\\textcolor{versoKeywordColor}{\\fontseries{b}\\fontshape{n}\\selectfont #1}}" &&
  hasSub p "\\definecolor{versoConstColor}{HTML}{0044BB}" &&
  hasSub p "\\renewcommand{\\versoConst}[1]{\\textcolor{versoConstColor}{\\fontseries{m}\\fontshape{it}\\selectfont #1}}"
