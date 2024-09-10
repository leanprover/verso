/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Data.Json
import Std.Data.HashMap
import SubVerso.Highlighting
import Verso.Method
import Verso.Output.Html

open SubVerso.Highlighting
open Verso.Output Html
open Lean (Json)
open Std (HashMap)


namespace Verso.Code

namespace Hover
structure Dedup (α) extends BEq α, Hashable α where
  nextId : Nat := 0
  contentId : HashMap Nat α := {}
  idContent : HashMap α Nat := {}

variable {α}

def Dedup.empty [BEq α] [Hashable α] : Dedup α := {}

instance [BEq α] [Hashable α] : Inhabited (Dedup α) where
  default := .empty

def Dedup.insert (table : Dedup α) (val : α) : Nat × Dedup α :=
  if let some id := table.idContent[val]? then (id, table)
  else
    let id := table.nextId
    let _ := table.toBEq
    let _ := table.toHashable
    (id, {table with
            nextId := id + 1,
            contentId := table.contentId.insert id val,
            idContent := table.idContent.insert val id})

def Dedup.get? (table : Dedup α) (id : Nat) : Option α := table.contentId[id]?

def Dedup.docJson (table : Dedup Html) : Json :=
  table.contentId.fold (init := .mkObj []) fun out id html => out.setObjVal! (toString id) (.str html.asString)

structure IdSupply where
  nextId : Nat := 0

def IdSupply.unique (supply : IdSupply) : String × IdSupply :=
  (s!"--verso-unique-{supply.nextId}", {supply with nextId := supply.nextId + 1})

structure State (α) where
  dedup : Dedup α
  idSupply : IdSupply

def State.empty [BEq α] [Hashable α] : State α := ⟨{}, {}⟩

instance [BEq α] [Hashable α] : EmptyCollection (State α) where
  emptyCollection := .empty

instance [BEq α] [Hashable α] : Inhabited (State α) where
  default := {}

end Hover

open Hover

open Lean (Name FVarId Level) in
structure LinkTargets where
  var : FVarId → Option String := fun _ => none
  sort : Level → Option String := fun _ => none
  const : Name → Option String := fun _ => none
  option : Name → Option String := fun _ => none
  keyword : Name → Option String := fun _ => none

inductive HighlightHtmlM.CollapseGoals where
  | subsequent
  | always
  | never

structure HighlightHtmlM.Options where
  inlineProofStates : Bool := true
  collapseGoals : CollapseGoals := .subsequent

structure HighlightHtmlM.Context where
  linkTargets : LinkTargets
  options : HighlightHtmlM.Options

abbrev HighlightHtmlM α := ReaderT HighlightHtmlM.Context (StateT (State Html) Id) α

def addHover (content : Html) : HighlightHtmlM Nat := modifyGet fun st =>
  let (hoverId, dedup) := st.dedup.insert content
  (hoverId, {st with dedup := dedup})

def uniqueId : HighlightHtmlM String := modifyGet fun st =>
  let (id, idSupply) := st.idSupply.unique
  (id, {st with idSupply := idSupply})

def withCollapsedSubgoals (policy : HighlightHtmlM.CollapseGoals) (act : HighlightHtmlM α) : HighlightHtmlM α :=
  withReader (fun ctx => {ctx with options := {ctx.options with collapseGoals := policy} }) act

def linkTargets : HighlightHtmlM LinkTargets := do
  return (← readThe HighlightHtmlM.Context).linkTargets

def options : HighlightHtmlM HighlightHtmlM.Options := do
  return (← readThe HighlightHtmlM.Context).options

open Lean in
open Verso.Output.Html in
def constLink (constName : Name) (content : Html) : HighlightHtmlM Html := do
  if let some tgt := (← linkTargets).const constName then
    pure {{<a href={{tgt}}>{{content}}</a>}}
  else
    pure content

open Lean in
open Verso.Output.Html in
def optionLink (optionName : Name) (content : Html) : HighlightHtmlM Html := do
  if let some tgt := (← linkTargets).option optionName then
    pure {{<a href={{tgt}}>{{content}}</a>}}
  else
    pure content

open Lean in
open Verso.Output.Html in
def varLink (varName : FVarId) (content : Html) : HighlightHtmlM Html := do
  if let some tgt := (← linkTargets).var varName then
    pure {{<a href={{tgt}}>{{content}}</a>}}
  else
    pure content

open Lean in
open Verso.Output.Html in
def kwLink (kind : Name) (content : Html) : HighlightHtmlM Html := do
  if let some tgt := (← linkTargets).keyword kind then
    pure {{<a href={{tgt}}>{{content}}</a>}}
  else
    pure content


defmethod Token.Kind.addLink (tok : Token.Kind) (content : Html) : HighlightHtmlM Html := do
  match tok with
  | .const x .. => constLink x content
  | .option o .. => optionLink o content
  | .var x .. => varLink x content
  | .keyword (some k) .. => kwLink k content
  | _ => pure content

partial defmethod Highlighted.isEmpty (hl : Highlighted) : Bool :=
  match hl with
  | .text str => str.isEmpty
  | .token .. => false
  | .span _ hl => hl.isEmpty
  | .tactics _ _ _ hl => hl.isEmpty
  | .point .. => true
  | .seq hls => hls.all isEmpty

partial defmethod Highlighted.trimRight (hl : Highlighted) : Highlighted :=
  match hl with
  | .text str => .text str.trimRight
  | .token .. => hl
  | .span infos hl => .span infos hl.trimRight
  | .tactics info startPos endPos hl => .tactics info startPos endPos hl.trimRight
  | .point .. => hl
  | .seq hls => Id.run do
    let mut hls := hls
    repeat
      if h : hls.size > 0 then
        have : hls.size - 1 < hls.size := by
          apply Nat.sub_lt_of_pos_le
          . simp
          . exact h
        if hls[hls.size - 1].isEmpty then
          hls := hls.pop
        else break
      else break
    if h : hls.size > 0 then
      let i := hls.size - 1
      have : i < hls.size := by
        dsimp (config := {zetaDelta := true})
        apply Nat.sub_lt_of_pos_le
        . simp
        . exact h
      --dbg_trace repr hls[i]
      .seq <| hls.set ⟨i, by assumption⟩ hls[i].trimRight
    else hl

partial defmethod Highlighted.trimLeft (hl : Highlighted) : Highlighted :=
  match hl with
  | .text str => .text str.trimLeft
  | .token .. => hl
  | .span infos hl => .span infos hl.trimLeft
  | .tactics info startPos endPos hl => .tactics info startPos endPos hl.trimLeft
  | .point .. => hl
  | .seq hls =>
    if h : hls.size > 0 then
      .seq <| hls.set ⟨0, h⟩ hls[0].trimLeft
    else hl

defmethod Highlighted.trim (hl : Highlighted) : Highlighted := hl.trimLeft.trimRight

-- def hover (content : Html) : Html := {{
--   <span class="hover-container"><span class="hover-info"> {{ content }} </span></span>
-- }}

defmethod Token.Kind.hover? (tok : Token.Kind) : HighlightHtmlM (Option Nat) :=
  match tok with
  | .const _n sig doc =>
    let docs :=
      match doc with
      | none => .empty
      | some txt => separatedDocs txt
    some <$> addHover {{ <code>{{sig}}</code> {{docs}} }}
  | .option optName _declName doc =>
    let docs := match doc with
      | none => .empty
      | some txt => separatedDocs txt
    some <$> addHover {{ <code>{{toString optName}}</code> {{docs}} }}
  | .keyword _ _ none => pure none
  | .keyword _ _ (some doc) => some <$> addHover {{<code class="docstring">{{doc}}</code>}}
  | .var _ type =>
    some <$> addHover {{ <code>{{type}}</code> }}
  | .str s =>
    some <$> addHover {{ <code><span class="literal string">{{s.quote}}</span>" : String"</code>}}
  | _ => pure none
where
  separatedDocs txt :=
    {{<span class="sep"/><code class="docstring">{{txt}}</code>}}

defmethod Highlighted.Span.Kind.«class» : Highlighted.Span.Kind → String
  | .info => "info"
  | .warning => "warning"
  | .error => "error"

defmethod Token.Kind.«class» : Token.Kind → String
  | .var _ _ => "var"
  | .str _ => "literal string"
  | .sort  => "sort"
  | .const _ _ _ => "const"
  | .option _ _ _ => "option"
  | .docComment => "doc-comment"
  | .keyword _ _ _ => "keyword"
  | .unknown => "unknown"

defmethod Token.Kind.data : Token.Kind → String
  | .const n _ _ => "const-" ++ toString n
  | .var ⟨v⟩ _ => "var-" ++ toString v
  | .option n _ _ => "option-" ++ toString n
  | .keyword _ (some occ) _ => "kw-occ-" ++ toString occ
  | _ => ""

defmethod Token.toHtml (tok : Token) : HighlightHtmlM Html := do
  let hoverId ← tok.kind.hover?
  let hoverAttr := hoverId.map (fun i => #[("data-verso-hover", toString i)]) |>.getD #[]
  tok.kind.addLink {{
    <span class={{tok.kind.«class» ++ " token"}} "data-binding"={{tok.kind.data}} {{hoverAttr}}>{{tok.content}}</span>
  }}

defmethod Highlighted.Goal.toHtml (exprHtml : expr → HighlightHtmlM Html) (index : Nat) : Highlighted.Goal expr → HighlightHtmlM Html
  | {name, goalPrefix, hypotheses, conclusion} => do
    let hypsHtml : Html ←
      if hypotheses.size = 0 then pure .empty
      else pure {{
        <span class="hypotheses">
          {{← hypotheses.mapM fun
              | (x, k, t) => do pure {{
                  <span class="hypothesis">
                    <span class="name">{{← Token.toHtml ⟨k, x.toString⟩}}</span><span class="colon">":"</span>
                    <span class="type">{{← exprHtml t}}</span>
                  </span>
                }}
          }}
        </span>
      }}
    let conclHtml ← do pure {{
        <span class="conclusion">
          <span class="prefix">{{goalPrefix}}</span><span class="type">{{← exprHtml conclusion}}</span>
        </span>
      }}
    let collapsePolicy := (← options).collapseGoals
    let id ← uniqueId
    pure {{
      <span class="goal">
        {{ match name with
          | none => {{
             {{hypsHtml}}
             {{conclHtml}}
            }}
          | some n => {{
              <span class="labeled-case" {{openAttr collapsePolicy index}}>
                <label class="case-label">
                  <input type="checkbox" id={{id}} {{openAttr collapsePolicy index}}/>
                  <span for={{id}} class="goal-name">{{n.toString}}</span>
                </label>
               {{hypsHtml}}
               {{conclHtml}}
              </span>
            }}
        }}
      </span>
    }}
  where
    openAttr policy index :=
      match policy with
      | .always => #[]
      | .never => #[("checked", "checked")]
      | .subsequent => if index = 0 then #[("checked", "checked")] else #[]

def spanClass (infos : Array (Highlighted.Span.Kind × α)) : Option String := Id.run do
  let mut k := none
  for (k', _) in infos do
    if let some k'' := k then k := maxKind k' k''
    else k := k'
  k.map (·.«class»)
where
  maxKind : Highlighted.Span.Kind → Highlighted.Span.Kind → Highlighted.Span.Kind
    | .error, _ => .error
    | .warning, .error => .error
    | .warning, _ => .warning
    | .info, other => other

def _root_.Array.mapIndexed (arr : Array α) (f : Fin arr.size → α → β) : Array β := Id.run do
  let mut out := #[]
  for h : i in [:arr.size] do
    out := out.push (f ⟨i, h.right⟩ arr[i])
  out

def _root_.Array.mapIndexedM [Monad m] (arr : Array α) (f : Fin arr.size → α → m β) : m (Array β) := do
  let mut out := #[]
  for h : i in [:arr.size] do
    out := out.push (← f ⟨i, h.right⟩ arr[i])
  pure out


partial defmethod Highlighted.toHtml : Highlighted → HighlightHtmlM Html
  | .token t => t.toHtml
  | .text str => pure str
  | .span infos hl =>
    if let some cls := spanClass infos then do
      pure {{<span class={{"has-info " ++ cls}}>
          <span class="hover-container">
            <span class={{"hover-info messages"}}>
              {{ infos.map fun (s, info) => {{
                <code class={{"message " ++ s.«class»}}>{{info}}</code> }}
              }}
            </span>
          </span>
          {{← toHtml hl}}
        </span>
      }}
    else
      panic! "No highlights!"
      --toHtml hl
  | .tactics info startPos endPos hl => do
    if (← options).inlineProofStates then
      let id := s!"tactic-state-{hash info}-{startPos}-{endPos}"
      pure {{
        <span class="tactic">
          <label «for»={{id}}>{{← toHtml hl}}</label>
          <input type="checkbox" class="tactic-toggle" id={{id}}></input>
          <span class="tactic-state">
            {{← if info.isEmpty then
                pure {{"All goals completed! 🐙"}}
              else
                .seq <$> info.mapIndexedM (fun ⟨i, _⟩ x => x.toHtml toHtml i)}}
          </span>
        </span>
      }}
    else
      toHtml hl
  | .point s info => pure {{<span class={{"message " ++ s.«class»}}>{{info}}</span>}}
  | .seq hls => hls.mapM toHtml

defmethod Highlighted.blockHtml (contextName : String) (code : Highlighted) : HighlightHtmlM Html := do
  pure {{ <code class="hl lean block" "data-lean-context"={{toString contextName}}> {{ ← code.trim.toHtml }} </code> }}

defmethod Highlighted.inlineHtml (contextName : Option String) (code : Highlighted) : HighlightHtmlM Html := do
  if let some ctx := contextName then
    pure {{ <code class="hl lean inline" "data-lean-context"={{toString ctx}}> {{ ← code.trim.toHtml }} </code> }}
  else
    pure {{ <code class="hl lean inline"> {{ ← code.trim.toHtml }} </code> }}

-- TODO CSS variables, and document them
def highlightingStyle : String := "

.hl.lean {
  white-space: pre;
  font-weight: normal;
  font-style: normal;
}

.hl.lean .keyword {
  font-weight : bold;
}

.hl.lean .var {
  font-style: italic;
  position: relative;
}

.hover-container {
  width: 0;
  height: 0;
  position: relative;
  display: inline;
}

.hl.lean a {
  color: inherit;
  text-decoration: currentcolor underline dotted;
}

.hl.lean a:hover {
  text-decoration: currentcolor underline solid;
}

.hl.lean .hover-info {
  white-space: normal;
}

.hl.lean .token .hover-info {
  display: none;
  position: absolute;
  background-color: #e5e5e5;
  border: 1px solid black;
  padding: 0.5em;
  z-index: 300;
  font-size: inherit;
}

.hl.lean .hover-info.messages {
  max-height: 10em;
  overflow-y: auto;
  overflow-x: hidden;
  scrollbar-gutter: stable;
  padding: 0 0.5em 0 0;
  display: block;
}

.hl.lean .hover-info code {
  white-space: pre-wrap;
}

.hl.lean .hover-info.messages > code {
  padding: 0.5em;
  display: block;
  width: fit-content;
}

.hl.lean .hover-info.messages > code:only-child {
  margin: 0;
}

.hl.lean .hover-info.messages > code {
  margin: 0.1em;
}

.hl.lean .hover-info.messages > code:not(:first-child) {
  margin-top: 0em;
}

/*
@media (hover: hover) {
  .hl.lean .has-info:hover > .hover-container > .hover-info:not(.tactic *),
  .hl.lean .tactic:has(> .tactic-toggle:checked) .has-info:hover > .hover-container > .hover-info,
  .hl.lean .token:hover > .hover-container > .hover-info:not(.has-info *):not(.tactic *),
  .hl.lean .tactic:has(> .tactic-toggle:checked) .token:hover > .hover-container > .hover-info:not(.has-info *) {
    display: inline-block;
    position: absolute;
    top: 1em;
    font-weight: normal;
    font-style: normal;
    width: min-content;
  }
}
*/

.hl.lean.block {
  display: block;
}

.hl.lean.inline {
  display: inline;
}

.hl.lean .token {
  transition: all 0.25s; /* Slight fade for highlights */
}

@media (hover: hover) {
  .hl.lean .token.binding-hl, .hl.lean .literal.string:hover {
    background-color: #eee;
    border-radius: 2px;
    transition: none;
  }
}


.hl.lean .has-info {
  text-decoration-style: wavy;
  text-decoration-line: underline;
  text-decoration-thickness: 0.1rem;
}

.hl.lean .has-info .hover-info {
  display: none;
  position: absolute;
  transform: translate(0.25rem, 0.3rem);
  border: 1px solid black;
  padding: 0.5em;
  z-index: 400;
  text-align: left;
}

.hl.lean .has-info.error {
  text-decoration-color: red;
}

@media (hover: hover) {
  .hl.lean .has-info.error:hover {
    background-color: #ffb3b3;
  }
}

.hl.lean .hover-info.messages > code.error {
  background-color: #e5e5e5;
  border-left: 0.2em solid #ffb3b3;
}

.tippy-box[data-theme~='error'] .hl.lean .hover-info.messages > code.error {
  background: none;
  border: none;
}

.error pre {
    color: red;
}

.hl.lean .has-info.warning {
  text-decoration-color: #efd871;
}

@media (hover: hover) {
  .hl.lean .has-info.warning:hover {
    background-color: #efd871;
  }
}

.hl.lean .hover-info.messages > code.warning {
  background-color: #efd871;
}

.hl.lean .hover-info.messages > code.error {
  background-color: #e5e5e5;
  border-left: 0.2em solid #efd871;
}

.tippy-box[data-theme~='warning'] .hl.lean .hover-info.messages > code.warning {
  background: none;
  border: none;
}


.hl.lean .has-info.info {
  text-decoration-color: blue;
}

@media (hover: hover) {
  .hl.lean .has-info.info:hover {
    background-color: #4777ff;
  }
}


.hl.lean .hover-info.messages > code.info {
  background-color: #e5e5e5;
  border-left: 0.2em solid #4777ff;
}

.tippy-box[data-theme~='info'] .hl.lean .hover-info.messages > code.info {
  background: none;
  border: none;
}

.hl.lean div.docstring {
  font-family: sans-serif;
  white-space: normal;
  max-width: 40em;
  width: max-content;
}

.hl.lean div.docstring > :last-child {
  margin-bottom: 0;
}

.hl.lean .hover-info .sep {
  display: block;
  width: auto;
  margin-left: 1em;
  margin-right: 1em;
  margin-top: 0.5em;
  margin-bottom: 0.5em;
  padding: 0;
  height: 1px;
  border-top: 1px solid #ccc;
}

.hl.lean code {
  font-family: monospace;
}

.hl.lean .tactic-state {
  display: none;
  position: relative;
  left: 2em;
  width: fit-content;
  border: 1px solid #888888;
  border-radius: 0.1em;
  padding: 0.5em;
  font-family: sans-serif;
  background-color: #ffffff;
  z-index: 200;
}

.hl.lean.popup .tactic-state {
  position: static;
  display: block;
  width: auto;
  border: none;
  padding: 0.5em;
  font-family: sans-serif;
  background-color: #ffffff;
}


.hl.lean .tactic {
  position: relative;
}

.hl.lean .tactic-toggle:checked ~ .tactic-state {
  display: block;
}

/*
@media (hover: hover) {
  .hl.lean .tactic:hover > .tactic-toggle:not(:checked) ~ .tactic-state {
    display: block;
    position: absolute;
    left: 0;
    transform: translate(0.25rem, 0);
    z-index: 250;
  }
}
*/

.hl.lean .tactic > label {
  position: relative;
  transition: all 0.5s;
}

@media (hover: hover) {
  .hl.lean .tactic > label:hover {
    border-bottom: 1px dotted #bbbbbb;
  }
}

.hl.lean .tactic-toggle {
  position: absolute;
  top: 0;
  left: 0;
  opacity: 0;
  height: 0;
  width: 0;
  z-index: -10;
}

.hl.lean .tactic > label::after {
  content: \"\";
  border: 1px solid #bbbbbb;
  border-radius: 1em;
  height: 0.25em;
  vertical-align: middle;
  width: 0.6em;
  margin-left: 0.1em;
  margin-right: 0.1em;
  display: inline-block;
  transition: all 0.5s;
}

/*
@media (hover: hover) {
  .hl.lean .tactic > label:hover::after {
    border: 1px solid #aaaaaa;
    background-color: #aaaaaa;
    transition: all 0.5s;
  }
}
*/

.hl.lean .tactic > label:has(+ .tactic-toggle:checked)::after {
  border: 1px solid #999999;
  background-color: #999999;
  transition: all 0.5s;
}

.hl.lean .tactic-state .goal + .goal {
  margin-top: 1.5em;
}

.hl.lean .tactic-state summary {
  margin-left: -0.5em;
}

.hl.lean .tactic-state details {
  padding-left: 0.5em;
}

.hl.lean .case-label {
  display: block;
  position: relative;
}

.hl.lean .case-label input[type=\"checkbox\"] {
  position: absolute;
  top: 0;
  left: 0;
  opacity: 0;
  height: 0;
  width: 0;
  z-index: -10;
}

.hl.lean .case-label:has(input[type=\"checkbox\"])::before {
  width: 1em;
  height: 1em;
  display: inline-block;
  background-color: black;
  content: ' ';
  transition: ease 0.2s;
  margin-right: 0.7em;
  clip-path: polygon(100% 0, 0 0, 50% 100%);
  width: 0.6em;
  height: 0.6em;
}

.hl.lean .case-label:has(input[type=\"checkbox\"]:not(:checked))::before {
  transform: rotate(-90deg);
}

.hl.lean .case-label:has(input[type=\"checkbox\"]) {

}

.hl.lean .case-label:has(input[type=\"checkbox\"]:checked) {

}


.hl.lean .tactic-state .labeled-case > :not(:first-child) {
  max-height: 0px;
  display: block;
  overflow: hidden;
  transition: max-height 0.1s ease-in;
  margin-left: 0.5em;
  margin-top: 0.1em;
}

.hl.lean .labeled-case:has(.case-label input[type=\"checkbox\"]:checked) > :not(:first-child) {
  max-height: 100%;
}


.hl.lean .tactic-state .goal-name::before {
  font-style: normal;
  content: \"case \";
}

.hl.lean .tactic-state .goal-name {
  font-style: italic;
  font-family: monospace;
}

.hl.lean .tactic-state .hypotheses {
  display: table;
}

.hl.lean .tactic-state .hypothesis {
  display: table-row;
}

.hl.lean .tactic-state .hypothesis > * {
  display: table-cell;
}


.hl.lean .tactic-state .hypotheses .colon {
  text-align: center;
  min-width: 1em;
}

.hl.lean .tactic-state .hypotheses .name {
  text-align: right;
}

.hl.lean .tactic-state .hypotheses .name,
.hl.lean .tactic-state .hypotheses .type,
.hl.lean .tactic-state .conclusion .type {
  font-family: monospace;
}

.tippy-box[data-theme~='lean'] {
  background-color: #e5e5e5;
  color: black;
  border: 1px solid black;
}
.tippy-box[data-theme~='lean'][data-placement^='top'] > .tippy-arrow::before {
  border-top-color: #e5e5e5;
}
.tippy-box[data-theme~='lean'][data-placement^='bottom'] > .tippy-arrow::before {
  border-bottom-color: #e5e5e5;
}
.tippy-box[data-theme~='lean'][data-placement^='left'] > .tippy-arrow::before {
  border-left-color: #e5e5e5;
}
.tippy-box[data-theme~='lean'][data-placement^='right'] > .tippy-arrow::before {
  border-right-color: #e5e5e5;
}

.tippy-box[data-theme~='message'][data-placement^='top'] > .tippy-arrow::before {
  border-top-color: #e5e5e5;
  border-width: 11px 11px 0;
}
.tippy-box[data-theme~='message'][data-placement^='top'] > .tippy-arrow::after {
  bottom: -11px;
  border-width: 11px 11px 0;
}
.tippy-box[data-theme~='message'][data-placement^='bottom'] > .tippy-arrow::before {
  border-width: 0 11px 11px;
}
.tippy-box[data-theme~='message'][data-placement^='bottom'] > .tippy-arrow::after {
  top: -11px;
  border-width: 0 11px 11px;
}
.tippy-box[data-theme~='message'][data-placement^='left'] > .tippy-arrow::before {
  border-left-color: #e5e5e5;
  border-width: 11px 0 11px 11px;
}
.tippy-box[data-theme~='message'][data-placement^='left'] > .tippy-arrow::after {
  right: -11px;
  border-width: 11px 0 11px 11px;
}

.tippy-box[data-theme~='message'][data-placement^='right'] > .tippy-arrow::before {
  border-right-color: #e5e5e5;
  border-width: 11px 11px 11px 0;
}
.tippy-box[data-theme~='message'][data-placement^='right'] > .tippy-arrow::after {
  left: -11px;
  border-width: 11px 11px 11px 0;
}



.tippy-box[data-theme~='warning'] {
  background-color: #e5e5e5;
  color: black;
  border: 3px solid #efd871;
}

.tippy-box[data-theme~='error'] {
  background-color: #e5e5e5;
  color: black;
  border: 3px solid #f7a7af;
}

.tippy-box[data-theme~='info'] {
  background-color: #e5e5e5;
  color: black;
  border: 3px solid #99b3c2;
}



.tippy-box[data-theme~='tactic'] {
  background-color: white;
  color: black;
  border: 1px solid black;
}
.tippy-box[data-theme~='tactic'][data-placement^='top'] > .tippy-arrow::before {
  border-top-color: white;
}
.tippy-box[data-theme~='tactic'][data-placement^='bottom'] > .tippy-arrow::before {
  border-bottom-color: white;
}
.tippy-box[data-theme~='tactic'][data-placement^='left'] > .tippy-arrow::before {
  border-left-color: white;
}
.tippy-box[data-theme~='tactic'][data-placement^='right'] > .tippy-arrow::before {
  border-right-color: white;
}

"

def highlightingJs : String :=
"
window.onload = () => {

    // Don't show hovers inside of closed tactic states
    function blockedByTactic(elem) {
      let parent = elem.parentNode;
      while (parent && \"classList\" in parent) {
        if (parent.classList.contains(\"tactic\")) {
          const toggle = parent.querySelector(\"input.tactic-toggle\");
          if (toggle) {
            return !toggle.checked;
          }
        }
        parent = parent.parentNode;
      }
      return false;
    }

    function blockedByTippy(elem) {
      // Don't show a new hover until the old ones are all closed.
      // Scoped to the nearest \"top-level block\" to avoid being O(n) in the size of the document.
      var block = elem;
      const topLevel = new Set([\"section\", \"body\", \"html\", \"nav\", \"header\"]);
      while (block.parentNode && !topLevel.has(block.parentNode.nodeName.toLowerCase())) {
        block = block.parentNode;
      }
      for (const child of block.querySelectorAll(\".token, .has-info\")) {
        if (child._tippy && child._tippy.state.isVisible) { return true };
      }
      return false;
    }

    for (const c of document.querySelectorAll(\".hl.lean .token\")) {
        if (c.dataset.binding != \"\") {
            c.addEventListener(\"mouseover\", (event) => {
                if (blockedByTactic(c)) {return;}
                const context = c.closest(\".hl.lean\").dataset.leanContext;
                for (const example of document.querySelectorAll(\".hl.lean\")) {
                    if (example.dataset.leanContext == context) {
                        for (const tok of example.querySelectorAll(\".token\")) {
                            if (c.dataset.binding == tok.dataset.binding) {
                                tok.classList.add(\"binding-hl\");
                            }
                        }
                    }
                }
            });
        }
        c.addEventListener(\"mouseout\", (event) => {
            for (const tok of document.querySelectorAll(\".hl.lean .token\")) {
                tok.classList.remove(\"binding-hl\");
            }
        });
    }
    /* Render docstrings */
    if ('undefined' !== typeof marked) {
        for (const d of document.querySelectorAll(\"code.docstring, pre.docstring\")) {
            const str = d.innerText;
            const html = marked.parse(str);
            const rendered = document.createElement(\"div\");
            rendered.classList.add(\"docstring\");
            rendered.innerHTML = html;
            d.parentNode.replaceChild(rendered, d);
        }
    }
    // Add hovers
    fetch(\"/-verso-docs.json\").then((resp) => resp.json()).then((versoDocData) => {

      const defaultTippyProps = {
        /* DEBUG -- remove the space: * /
        onHide(any) { return false; },
        trigger: \"click\",
        // */
        theme: \"lean\",
        maxWidth: \"none\",
        appendTo: () => document.body,
        interactive: true,
        delay: [100, null],
        ignoreAttributes: true,
        onShow(inst) {
          if (inst.reference.querySelector(\".hover-info\") || \"versoHover\" in inst.reference.dataset) {
            if (blockedByTactic(inst.reference)) { return false };
            if (blockedByTippy(inst.reference)) { return false; }
          } else { // Nothing to show here!
            return false;
          }
        },
        content (tgt) {
          const content = document.createElement(\"span\");
          content.className = \"hl lean\";
          content.style.display = \"block\";
          content.style.maxHeight = \"300px\";
          content.style.overflowY = \"auto\";
          content.style.overflowX = \"hidden\";
          const hoverId = tgt.dataset.versoHover;
          const hoverInfo = tgt.querySelector(\".hover-info\");
          if (hoverId) { // Docstrings from the table
            // TODO stop doing an implicit conversion from string to number here
            let data = versoDocData[hoverId];
            if (data) {
              const info = document.createElement(\"span\");
              info.className = \"hover-info\";
              info.style.display = \"block\";
              info.innerHTML = data;
              content.appendChild(info);
              /* Render docstrings - TODO server-side */
              if ('undefined' !== typeof marked) {
                  for (const d of content.querySelectorAll(\"code.docstring, pre.docstring\")) {
                      const str = d.innerText;
                      const html = marked.parse(str);
                      const rendered = document.createElement(\"div\");
                      rendered.classList.add(\"docstring\");
                      rendered.innerHTML = html;
                      d.parentNode.replaceChild(rendered, d);
                  }
              }
            } else {
              content.innerHTML = \"Failed to load doc ID: \" + hoverId;
            }
          } else if (hoverInfo) { // The inline info, still used for compiler messages
            content.appendChild(hoverInfo.cloneNode(true));
          }
          return content;
        }
      };

      const addTippy = (selector, props) => {
        tippy(selector, Object.assign({}, defaultTippyProps, props));
      };
      addTippy('.hl.lean .const.token, .hl.lean .keyword.token, .hl.lean .literal.token, .hl.lean .option.token', {theme: 'lean'});
      addTippy('.hl.lean .has-info.warning', {theme: 'warning message'});
      addTippy('.hl.lean .has-info.info', {theme: 'info message'});
      addTippy('.hl.lean .has-info.error', {theme: 'error message'});

      tippy('.hl.lean .tactic', {
        allowHtml: true,
        /* DEBUG -- remove the space: * /
        onHide(any) { return false; },
        trigger: \"click\",
        // */
        maxWidth: \"none\",
        onShow(inst) {
          const toggle = inst.reference.querySelector(\"input.tactic-toggle\");
          if (toggle && toggle.checked) {
            return false;
          }
          if (blockedByTippy(inst.reference)) { return false; }
        },
        theme: \"tactic\",
        placement: 'bottom-start',
        content (tgt) {
          const content = document.createElement(\"span\");
          const state = tgt.querySelector(\".tactic-state\").cloneNode(true);
          state.style.display = \"block\";
          content.appendChild(state);
          content.style.display = \"block\";
          content.className = \"hl lean popup\";
          return content;
        }
      });
  });
}
"
