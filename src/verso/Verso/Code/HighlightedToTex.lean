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

/-
These two theorems justify termination of `containsNewline` below
in the face of its use of `Array.any`. They can be removed if these
land in `lean4` proper.
-/
@[wf_preprocess] theorem any_wfParam {xs : Array α} {f : α → Bool} :
    (wfParam xs).any f = xs.attach.unattach.any f := by
  simp [wfParam]

@[wf_preprocess] theorem any_unattach {P : α → Prop} {xs : Array (Subtype P)} {f : α → Bool} :
    xs.unattach.any f = xs.any fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp [wfParam]

namespace SubVerso.Highlighting.Highlighted

private def trimOneLeadingNl : Highlighted → Highlighted
  | .text s => .text <| (s.dropPrefix "\n").copy
  | .unparsed s => .unparsed <| (s.dropPrefix "\n").copy
  | .seq xs =>
    let i? := xs.findIdx? (!·.isEmpty)
    match h : i? with
    | some i =>
      have : i < xs.size := (Array.findIdx?_eq_some_iff_findIdx_eq.mp h).left
      xs.extract (i+1) |>.foldl (init := trimOneLeadingNl xs[i]) (· ++ ·)
    | none => .empty
  | hl@(.point ..) | hl@(.token ..) => hl
  | .tactics i s e hl => .tactics i s e (trimOneLeadingNl hl)
  | .span i hl => .span i (trimOneLeadingNl hl)

private def trimOneTrailingNl : Highlighted → Highlighted
  | .text s => .text <| (s.dropSuffix "\n").copy
  | .unparsed s => .unparsed <| (s.dropSuffix "\n").copy
  | .seq xs =>
    let ni? := xs.reverse.findIdx? (!·.isEmpty)
    match h : ni? with
    | some ni =>
      let i := xs.size - ni - 1
      have := (Array.findIdx?_eq_some_iff_findIdx_eq.mp h).left
      have : i < xs.size := by grind
      .seq (xs.extract (stop := i) ++ #[trimOneTrailingNl xs[i]])
    | none => .empty
  | hl@(.point ..) | hl@(.token ..) => hl
  | .tactics i s e hl => .tactics i s e (trimOneTrailingNl hl)
  | .span i hl => .span i (trimOneTrailingNl hl)

def containsNewline (t : Highlighted) : Bool := match t with
  | .text s => s.contains '\n'
  | .unparsed s => s.contains '\n'
  | .seq xs => xs.any containsNewline
  | (.point ..) | (.token ..) => False
  | .tactics _ _ _ hl => hl.containsNewline
  | .span _ hl => hl.containsNewline
termination_by t

end SubVerso.Highlighting.Highlighted

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
