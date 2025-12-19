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

open SubVerso.Highlighting
open Verso.Doc.TeX (escapeForVerbatim verbatimInline GenreTeX TeXT)
open Verso.Output
open Lean (Json ToJson FromJson Quote)
open Std (HashMap)


namespace SubVerso.Highlighting

/--
Given an already escaped-for-verbatim string, and a token kind,
returns TeX to display that token appropriately syntax-highlighted.
-/
public def highlightToken : String → Token.Kind → TeX
| c, .keyword _ _ _ => .raw s!"\\textbf\{{c}}"
| c, .const _ _ _ _ => .raw c
| c, .anonCtor _ _ _ => .raw c
| c, .option _ _ _ => .raw c
| c, .var (.mk _) _ => .raw s!"\\textit\{{c}}"
| c, .str _ => .raw c
| c, .docComment => .raw c
| c, .sort _ => .raw c
| c, .levelVar _ => .raw c
| c, .levelConst _ => .raw c
| c, .moduleName _ => .raw c
| c, .levelOp _ => .raw c
| c, .withType _ => .raw c
| c, .unknown => .raw c

defmethod Highlighting.Token.toVerbatimTeX (t : Highlighting.Token) : Verso.Output.TeX :=
  highlightToken (escapeForVerbatim t.content) t.kind

open Verso.Output.TeX in
/--
Returns TeX that is appropriate for the content of a `\Verb` environment (from package `fancyvrb`)
with command characters `\`, `{`, and `}`.
-/
public defmethod Highlighted.toVerbatimTeX : Highlighted → Verso.Output.TeX
  | .token t => highlightToken (escapeForVerbatim t.content) t.kind
  | .text str => .raw (escapeForVerbatim str)
  | .seq hts => .seq <| hts.map (·.toVerbatimTeX)
  | .span info content =>
     if h : info.size > 0
     then .seq #[.raw s!"\\{info[0].1.toString}Decorate\{", content.toVerbatimTeX, .raw "}"]
     else content.toVerbatimTeX
  | .tactics _info _start _end content => content.toVerbatimTeX
  | .point _kind _info => \TeX{"[Point]"}
  | .unparsed str => .raw (escapeForVerbatim str)

def verbatimBlock (t : Verso.Output.TeX) : Verso.Output.TeX :=
  .seq #[.raw "\\begin{LeanVerbatim}\n", t, .raw "\n\\end{LeanVerbatim}\n"]

public defmethod Highlighting.Token.toTeX [Monad m] [GenreTeX g m] (t : Highlighting.Token) :
    TeXT g m Verso.Output.TeX :=
  verbatimInline (t.toVerbatimTeX)

public defmethod Highlighted.toTeX [Monad m] [GenreTeX g m] (t : Highlighted) :
    TeXT g m Verso.Output.TeX :=
  let strip := t.trimOneTrailingNl.trimOneLeadingNl
  if strip.isEmpty then
    pure .empty
  else if strip.containsNewline then
    pure <| verbatimBlock (strip.toVerbatimTeX)
  else
    verbatimInline (strip.toVerbatimTeX)


open Verso.Output.TeX in
public defmethod Highlighted.Goal.toTeX [Monad m] [GenreTeX g m] (h : Highlighted.Goal Highlighted) : TeXT g m Verso.Output.TeX := do
  let {name, goalPrefix, hypotheses, conclusion} := h
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

def messageContentsToVerbatimTeX [Monad m] [GenreTeX g m] (h : Highlighted.MessageContents Highlighted) : TeXT g m Verso.Output.TeX :=
  match h with
  | .text str => pure str
  | .goal g => pure g.toString
  | .term t => pure t.toVerbatimTeX
  | .trace _cls _msg _children _collapsed => pure .empty -- FIXME: what to render here?
  | .append mcs => do
      -- We are doing this two-step dance only because lean can't see termination
      -- when we directly call mcs.mapM messageContentsToVerbatimTeX. This probably
      -- wouldn't be necessary if there were appropriate @[wf_preprocess] lemmas for mapM.
      let contentsM := mcs.map messageContentsToVerbatimTeX
      let contents ← contentsM.mapM id
      pure (.seq contents)

public defmethod Highlighted.Message.toTeX [Monad m] [GenreTeX g m] (h : Highlighted.Message) : TeXT g m Verso.Output.TeX := do
  let {severity, contents} := h
  let rulecolor := s!"{severity}Color"
  let body ← messageContentsToVerbatimTeX contents
  pure <| .seq #[
    .raw s!"\\begin\{LeanVerbatim}[formatcom=\\color\{{rulecolor}}, framesep=2mm, vspace=0pt, framerule=1.25mm, frame=leftline]\n",
    body,
    .raw "\n\\end{LeanVerbatim}\n"
  ]
