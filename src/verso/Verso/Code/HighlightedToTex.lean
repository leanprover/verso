/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/
import SubVerso.Highlighting
import Verso.Method
import Verso.Output.TeX

open SubVerso.Highlighting
open Verso.Output
open Lean (Json ToJson FromJson Quote)
open Std (HashMap)

namespace SubVerso.Highlighting.Highlighted

def trimOneLeadingNl : Highlighted → Highlighted
  | .text s => .text <| if "\n".isPrefixOf s then s.drop 1 else s
  | .unparsed s => .unparsed <| if "\n".isPrefixOf s then s.drop 1 else s
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

def trimOneTrailingNl : Highlighted → Highlighted
  | .text s => .text <| s.stripSuffix "\n"
  | .unparsed s => .unparsed <| s.stripSuffix "\n"
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

end SubVerso.Highlighting.Highlighted

namespace SubVerso.Highlighting

/--
Given an already escaped-for-verbatim string, and a token kind,
returns TeX to display that token appropriately syntax-highlighted.
-/
def highlightToken : String → Token.Kind → TeX
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

/--
Replaces characters with strings simultaneously.
-/
def replaceChars (s : String) (replace : Char → Option String) : String :=
  let rec loop (acc : String) (pos : String.Pos.Raw) :=
    if pos.byteIdx ≥ s.utf8ByteSize then acc
    else
      have : (String.Pos.Raw.next s pos).byteIdx > pos.byteIdx :=
        String.Pos.Raw.byteIdx_lt_byteIdx_next s pos
      let c := pos.get s
      let s' := match replace c with | some rs => rs | none => s!"{c}"
      loop (acc ++ s') (pos.next s)
    termination_by s.endPos.1 - pos.1
  loop "" 0

/--
Escapes a string in an appropriate way for uses of
`\Verb[commandchars=\\\{\}]|...|` and
`\begin{Verbatim}[commandchars=\\\{\}]...\end{Verbatim}`
-/
def escapeForVerbatim (s : String) : String :=
  replaceChars s fun
  | '{' => some "\\symbol{123}"
  | '|' => some "\\symbol{124}"
  | '}' => some "\\symbol{125}"
  | '\\' => some "\\symbol{92}"
  -- The reason for changing U+271d LATIN CROSS to U+2020 DAGGER here
  -- is that DejaVu Sans Mono Oblique lacks the former, and we'd like
  -- to render variables in italic/oblique. If we decide on a
  -- different monospace font that has better coverage, we could
  -- reconsider this decision.
  -- Ordinarily it'd be pretty sketchy to subvert author intent by replacing
  -- characters that users might otherwise copy and paste into Lean,
  -- but this is exactly the character Lean inserts to create shadowed
  -- names, so it seems benign to change it in this case.
  | '✝' => some "†"
  | _ => none

/-- info: "\\symbol{123}\\symbol{124}\\symbol{125}\\symbol{92}" -/
#guard_msgs in
#eval escapeForVerbatim "{|}\\"

defmethod Highlighting.Token.toVerbatimTeX (t : Highlighting.Token) : Verso.Output.TeX :=
  highlightToken (escapeForVerbatim t.content) t.kind

open Verso.Output.TeX in
/--
Returns TeX that is appropriate for the content of a `\Verb` environment (from package `fancyvrb`)
with command characters `\`, `{`, and `}`.
-/
defmethod Highlighted.toVerbatimTeX : Highlighted → Verso.Output.TeX
  | .token t => highlightToken (escapeForVerbatim t.content) t.kind
  | .text str => .raw (escapeForVerbatim str)
  | .seq hts => .seq <| hts.map (·.toVerbatimTeX)
  | .span info content =>
     if h : info.size > 0
     then .seq #[.raw s!"\\{info[0].1.toString}Decorate\{", content.toVerbatimTeX, .raw "}"]
     else content.toVerbatimTeX
  | .tactics _info _start _end content => content.toVerbatimTeX
  | .point _kind _info => \TeX{"[Point]"}
  | .unparsed str => .raw (escapeForVerbatim str) -- FIXME: Is this right?

def verbatim (t : Verso.Output.TeX) : Verso.Output.TeX :=
  .seq #[.raw "\\LeanVerb|", t, .raw "|"]

defmethod Highlighting.Token.toTeX (t : Highlighting.Token) : Verso.Output.TeX :=
  verbatim (t.toVerbatimTeX)

defmethod Highlighted.toTeX (t : Highlighted) : Verso.Output.TeX :=
  let strip := t.trimOneTrailingNl
  if strip.isEmpty then
    .empty
  else
    verbatim (strip.toVerbatimTeX)

open Verso.Output.TeX in
defmethod Highlighted.Goal.toTeX (h : Highlighted.Goal Highlighted) : Id Verso.Output.TeX := do
  let {name, goalPrefix, hypotheses, conclusion} := h
  let mut rows : Array TeX := #[]
  if let some n := name then
    rows := rows ++ #[\TeX{\textbf{"case"} " " \Lean{n}}]
  let toRow (h : Highlighted.Hypothesis Highlighted) : TeX :=
    let namesTeX := h.names.map (·.toTeX) |>.toList.intersperse (.text " ")
    .seq #[namesTeX, .text " : ", h.typeAndVal.toTeX]
  rows := rows ++ hypotheses.map toRow
  rows := rows ++ #[verbatim (goalPrefix) ++ conclusion.toTeX]
  \TeX{\begin{tabular}{"l"} \Lean{rows.map (· ++ .raw "\\\\")} \end{tabular}}

def messageContentsToVerbatimTeX (h : Highlighted.MessageContents Highlighted) : Verso.Output.TeX :=
  match h with
  | .text str => str
  | .goal g => g.toTeX -- FIXME: this doesn't seem correct?
  | .term t => t.toVerbatimTeX
  | .trace _cls _msg _children _collapsed => .empty -- FIXME: what to render here?
  | .append mcs => .seq (mcs.map messageContentsToVerbatimTeX)

defmethod Highlighted.Message.toTeX (h : Highlighted.Message) : Verso.Output.TeX :=
  let {severity, contents} := h
  let rulecolor := s!"{severity}Color"
  let body := messageContentsToVerbatimTeX contents
  .seq #[
    .raw s!"\\begin\{LeanVerbatim}[formatcom=\\color\{{rulecolor}}, framesep=2mm, vspace=0pt, framerule=1.25mm, frame=leftline]\n",
    body,
    .raw "\n\\end{LeanVerbatim}\n"
  ]
