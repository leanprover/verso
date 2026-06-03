/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/
module
public import SubVerso.Highlighting
import Verso.Method
public import Verso.Output.TeX
public import Verso.Doc.TeX
public import Verso.Code.Highlighted

open SubVerso.Highlighting
open Verso.Doc.TeX (escapeForVerbatim verbatimInline GenreTeX TeXT)
open Verso.Output
open Lean (Json ToJson FromJson Quote)
open Std (HashMap)


namespace SubVerso.Highlighting

/--
Given an already escaped-for-verbatim string, and a token kind, returns TeX that wraps the
content in the matching semantic macro: `\versoKeyword`, `\versoConst`, `\versoVar`, or
`\versoLiteral`. The macros are defined by the consuming genre's preamble (the manual genre
uses {name}`Verso.Theme.CodeTheme` to style them). For a fallback definition that
reproduces the pre-theming look, see {name}`texMacroFallbacks`.
-/
public def highlightToken : String → Token.Kind → TeX
| c, .keyword _ _ _ => .raw s!"\\versoKeyword\{{c}}"
| c, .const .. => .raw s!"\\versoConst\{{c}}"
| c, .anonCtor .. => .raw s!"\\versoConst\{{c}}"
| c, .option _ _ _ => .raw s!"\\versoConst\{{c}}"
| c, .var .. => .raw s!"\\versoVar\{{c}}"
| c, .str _ => .raw s!"\\versoLiteralString\{{c}}"
| c, .docComment => .raw s!"\\versoDocComment\{{c}}"
| c, .sort _ => .raw s!"\\versoSort\{{c}}"
| c, .levelVar _ => .raw s!"\\versoLevelVar\{{c}}"
| c, .levelConst _ => .raw s!"\\versoLevelConst\{{c}}"
| c, .moduleName _ => .raw s!"\\versoModuleName\{{c}}"
| c, .levelOp _ => .raw s!"\\versoLevelOp\{{c}}"
| c, .withType _ => .raw s!"\\versoLiteral\{{c}}"
-- Built-in delimiters (`:=`, `=>`, `←`, `@`, `:`, `|`) and the three punctuation buckets
-- (operator / bracket / separator) each get their own semantic macro; the manual preamble
-- ties them to `delim`/`operator`/`bracket`/`separator` `TokenStyle` fields, which by
-- default cascade from `delim` and thus from the body code color.
| c, .delim .. => .raw s!"\\versoDelim\{{c}}"
| c, .operator .. => .raw s!"\\versoOperator\{{c}}"
| c, .bracket .. => .raw s!"\\versoBracket\{{c}}"
| c, .separator .. => .raw s!"\\versoSeparator\{{c}}"
-- The remaining lexical-ish kinds added by SubVerso (wildcard, num, char, line/block
-- comments, comment delimiter) currently route through `\versoLiteral` so PDF output keeps
-- the "default to the unknown/code appearance" semantics the HTML side gives them via its
-- lexical-default CSS rule. They are likely to gain their own theme buckets (numbers,
-- characters, comments) in a later phase.
| c, .wildcard .. => .raw s!"\\versoLiteral\{{c}}"
| c, .num .. => .raw s!"\\versoLiteral\{{c}}"
| c, .char .. => .raw s!"\\versoLiteral\{{c}}"
| c, .lineComment => .raw s!"\\versoLiteral\{{c}}"
| c, .blockComment => .raw s!"\\versoLiteral\{{c}}"
| c, .commentDelim => .raw s!"\\versoLiteral\{{c}}"
| c, .unknown => .raw s!"\\versoLiteral\{{c}}"

/--
Fallback definitions for the semantic token macros emitted by
{name}`SubVerso.Highlighting.highlightToken`. Each uses `\providecommand`, so a genre
preamble that defines its own (theme-driven) versions wins. The fallbacks reproduce today's
unthemed look: keywords bold, variables italic, constants and literals plain, doc comments
italic.
-/
public def texMacroFallbacks : String :=
"\\providecommand{\\versoKeyword}[1]{\\textbf{#1}}\n" ++
"\\providecommand{\\versoConst}[1]{#1}\n" ++
"\\providecommand{\\versoVar}[1]{\\textit{#1}}\n" ++
"\\providecommand{\\versoLiteral}[1]{#1}\n" ++
"\\providecommand{\\versoLiteralString}[1]{#1}\n" ++
"\\providecommand{\\versoDocComment}[1]{\\textit{#1}}\n" ++
"\\providecommand{\\versoSort}[1]{#1}\n" ++
"\\providecommand{\\versoLevelVar}[1]{\\textit{#1}}\n" ++
"\\providecommand{\\versoLevelConst}[1]{#1}\n" ++
"\\providecommand{\\versoLevelOp}[1]{#1}\n" ++
"\\providecommand{\\versoModuleName}[1]{#1}\n" ++
"\\providecommand{\\versoDelim}[1]{#1}\n" ++
"\\providecommand{\\versoOperator}[1]{#1}\n" ++
"\\providecommand{\\versoBracket}[1]{#1}\n" ++
"\\providecommand{\\versoSeparator}[1]{#1}\n"

defmethod Highlighting.Token.toVerbatimTeX (t : Highlighting.Token) (lineBreaks : Bool := false) : Verso.Output.TeX :=
  highlightToken (escapeForVerbatim t.content lineBreaks) t.kind

open Verso.Output.TeX in
/--
Returns TeX that is appropriate for the content of a `\Verb` environment (from package `fancyvrb`)
with command characters `\`, `{`, and `}`.

When `lineBreaks` is true, inserts line break opportunities in identifiers.

**Preamble contract.** Output uses the four `\verso…` semantic macros emitted by
{name}`SubVerso.Highlighting.highlightToken`. Any consumer that compiles the result must
ensure those macros are defined, either by including
{name}`SubVerso.Highlighting.texMacroFallbacks` in the preamble or by defining its own
theme-driven versions (the manual genre installs both).
-/
public defmethod Highlighted.toVerbatimTeX (h : Highlighted) (lineBreaks : Bool := false) : Verso.Output.TeX :=
  match h with
  | .token t => highlightToken (escapeForVerbatim t.content lineBreaks) t.kind
  | .text str => .raw (escapeForVerbatim str lineBreaks)
  | .seq hts => .seq <| hts.map (·.toVerbatimTeX lineBreaks)
  | .span info content =>
     if h : info.size > 0
     then .seq #[.raw s!"\\{info[0].1.toString}Decorate\{", content.toVerbatimTeX lineBreaks, .raw "}"]
     else content.toVerbatimTeX lineBreaks
  | .tactics _info _start _end content => content.toVerbatimTeX lineBreaks
  | .point _kind _info => \TeX{"[Point]"}
  | .unparsed str => .raw (escapeForVerbatim str lineBreaks)

def verbatimBlock (t : Verso.Output.TeX) : Verso.Output.TeX :=
  .seq #[.raw "\\begin{LeanVerbatim}\n", t, .raw "\n\\end{LeanVerbatim}\n"]

public defmethod Highlighting.Token.toTeX [Monad m] [GenreTeX g m] (t : Highlighting.Token) :
    TeXT g m Verso.Output.TeX :=
  verbatimInline (t.toVerbatimTeX (lineBreaks := true))

public defmethod Highlighted.toTeX [Monad m] [GenreTeX g m] (t : Highlighted) :
    TeXT g m Verso.Output.TeX :=
  let strip := t.trimOneTrailingNl.trimOneLeadingNl
  if strip.isEmpty then
    pure .empty
  else if strip.containsNewline then
    pure <| verbatimBlock (strip.toVerbatimTeX (lineBreaks := false))
  else
    verbatimInline (strip.toVerbatimTeX (lineBreaks := true))


open Verso.Output.TeX in
public defmethod Highlighted.Goal.toTeX [Monad m] [GenreTeX g m] (h : Highlighted.Goal Highlighted) : TeXT g m Verso.Output.TeX := do
  let {name, goalPrefix, hypotheses, conclusion, ..} := h
  let mut rows : Array TeX := #[]
  let verbatim (t : Verso.Output.TeX) : Verso.Output.TeX :=
    .seq #[.raw "\\LeanVerb|", t, .raw "|"]
  if let some n := name then
    rows := rows ++ #[\TeX{\textbf{"case"} " " \Lean{n}}]

  let toRow (h : Highlighted.Hypothesis Highlighted) : TeXT g m Verso.Output.TeX  := do
    let namesTeX := (← h.names.mapM (·.toTeX)).toList.intersperse (.text " ")
    pure <| .seq #[namesTeX, .text " : ", (← h.typeAndVal.toTeX)]
  rows := rows ++ (← hypotheses.mapM toRow)
  rows := rows ++ #[verbatim (goalPrefix) ++ (← conclusion.toTeX)]
  pure \TeX{\begin{tabular}{"l"} \Lean{rows.map (· ++ .raw r#"\\"#)} \end{tabular}}

open Verso.Output.TeX in
partial def messageContentsToVerbatimTeX [Monad m] [GenreTeX g m] (h : Highlighted.MessageContents Highlighted) (expandTraces : List Lean.Name := []): TeXT g m Verso.Output.TeX :=
  match h with
  | .text str => pure str
  | .goal g => pure g.toString
  | .term t => pure t.toVerbatimTeX
  | .trace cls msg children collapsed => do
    let thisMsg ← messageContentsToVerbatimTeX msg
    if !collapsed || cls ∈ expandTraces then
      return \TeX{
        \begin{expandedtrace}{\Lean{thisMsg}}
          \Lean{← children.mapM messageContentsToVerbatimTeX}
        \end{expandedtrace}
      }
    else
      return \TeX{
        \begin{collapsedtrace}{\Lean{thisMsg}}
        \end{collapsedtrace}
      }

  | .append mcs => do
      -- We are doing this two-step dance only because lean can't see termination
      -- when we directly call mcs.mapM messageContentsToVerbatimTeX. This probably
      -- wouldn't be necessary if there were appropriate @[wf_preprocess] lemmas for mapM.
      let contentsM := mcs.map messageContentsToVerbatimTeX
      let contents ← contentsM.mapM id
      pure (.seq contents)

public defmethod Highlighted.Message.toTeX [Monad m] [GenreTeX g m] (h : Highlighted.Message) (expandTraces : List Lean.Name := []) : TeXT g m Verso.Output.TeX := do
  let {severity, contents} := h
  -- These colors are defined in our standard LaTeX preamble as `errorColor`, `warningColor`, and `infoColor`
  let rulecolor := s!"{severity}Color"
  let body ← messageContentsToVerbatimTeX contents expandTraces
  pure <| .seq #[
    .raw s!"\\begin\{LeanVerbatim}[formatcom=\\color\{{rulecolor}}, framesep=2mm, vspace=0pt, framerule=1.25mm, frame=leftline]\n",
    body,
    .raw "\n\\end{LeanVerbatim}\n"
  ]

public defmethod Highlighted.Message.toTeXInlinePlain [Monad m] [GenreTeX g m] (h : Highlighted.Message) (expandTraces : List Lean.Name := []) : TeXT g m Verso.Output.TeX := do
  pure <| .seq #[
    .raw r#"\LeanVerb|"#,
    escapeForVerbatim <| h.contents.toString expandTraces,
    .raw "|"
  ]
