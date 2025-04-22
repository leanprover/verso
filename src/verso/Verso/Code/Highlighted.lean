/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Data.OpenDecl
import Lean.Data.Json
import Std.Data.HashMap
import SubVerso.Highlighting
import Verso.Method
import Verso.Output.Html

open SubVerso.Highlighting
open Verso.Output Html
open Lean (Json ToJson FromJson Quote)
open Std (HashMap)

namespace SubVerso.Highlighting

/--
Removes n levels of indentation from highlighted code.
-/
partial def Highlighted.deIndent (n : Nat) (hl : Highlighted) : Highlighted :=
  (remove hl).run' (some n)
where
  remove (hl : Highlighted) : StateM (Option Nat) Highlighted := do
    match hl with
    | .token t =>
      set (none : Option Nat)
      return .token t
    | .span i x => .span i <$> remove x
    | .seq xs => .seq <$> xs.mapM remove
    | .text s =>
      let mut s' := ""
      let mut iter := s.iter
      while h : iter.hasNext do
        let c := iter.curr' h
        iter := iter.next
        match c with
        | '\n' =>
          set (some n)
        | ' ' =>
          if let some (i + 1) ← get then
            set (some i)
            continue
        | _ => set (none : Option Nat)
        s' := s'.push c
      return .text s'
    | .point p s => return .point p s
    | .tactics gs x y hl => .tactics gs x y <$> remove hl

end SubVerso.Highlighting


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

def IdSupply.unique (supply : IdSupply) (base := "--verso-unique") : String × IdSupply :=
  (s!"{base}-{supply.nextId}", {supply with nextId := supply.nextId + 1})

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
  definition : Name → Option String := fun _ => none

inductive HighlightHtmlM.CollapseGoals where
  | subsequent
  | always
  | never

inductive HighlightHtmlM.VisibleProofStates where
  | none
  /--
  Make the given states visible.

  States are identified by the range included in the `Highlighted.tactics` constructor.
  -/
  | states (ranges : Array (Nat × Nat))
  | all
deriving ToJson, FromJson, Repr, Quote

def HighlightHtmlM.VisibleProofStates.isVisible : HighlightHtmlM.VisibleProofStates → Nat → Nat → Bool
  | .none, _, _ => false
  | .all, _, _ => true
  | .states xs, b, e => (b, e) ∈ xs

structure HighlightHtmlM.Options where
  inlineProofStates : Bool := true
  visibleProofStates : VisibleProofStates := .none
  collapseGoals : CollapseGoals := .subsequent

structure HighlightHtmlM.Context where
  linkTargets : LinkTargets
  definitionIds : Lean.NameMap String
  options : HighlightHtmlM.Options

/--
Monad used to render highlighted Verso code to HTML.

The monad enables the following features:
1. Conveying options of type `HighlightHtmlM.Options` that govern the display of a particular piece of code.
2. Conveying document-wide configurations, in particular policies for hyperlinking identifiers.
3. De-duplicating hovers, which can greatly reduce the size of generated HTML.
-/
abbrev HighlightHtmlM α := ReaderT HighlightHtmlM.Context (StateT (State Html) Id) α

def addHover (content : Html) : HighlightHtmlM Nat := modifyGet fun st =>
  let (hoverId, dedup) := st.dedup.insert content
  (hoverId, {st with dedup := dedup})

def uniqueId (base := "--verso-unique") : HighlightHtmlM String := modifyGet fun st =>
  let (id, idSupply) := st.idSupply.unique (base := base)
  (id, {st with idSupply := idSupply})

def withCollapsedSubgoals (policy : HighlightHtmlM.CollapseGoals) (act : HighlightHtmlM α) : HighlightHtmlM α :=
  withReader (fun ctx => {ctx with options := {ctx.options with collapseGoals := policy} }) act

def withVisibleProofStates (policy : HighlightHtmlM.VisibleProofStates) (act : HighlightHtmlM α) : HighlightHtmlM α :=
  withReader (fun ctx => {ctx with options := {ctx.options with visibleProofStates := policy} }) act

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

open Lean in
open Verso.Output.Html in
def defLink (defName : Name) (content : Html) : HighlightHtmlM Html := do
  if let some tgt := (← linkTargets).definition defName then
    pure {{<a href={{tgt}}>{{content}}</a>}}
  else
    pure content

defmethod Token.Kind.addLink (tok : Token.Kind) (content : Html) : HighlightHtmlM Html := do
  match tok with
  | .const x _ _ false => constLink x content
  | .const x _ _ true => defLink x content
  | .option o .. => optionLink o content
  | .var x .. => varLink x content
  | .keyword (some k) .. => kwLink k content
  | _ => pure content

/--
Removes trailing whitespace from highlighted code.
-/
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
      if let some last := hls.back? then
        let last := last.trimRight
        if last.isEmpty then
          hls := hls.pop
        else
          hls := hls.set! (hls.size - 1) last
          break
      else break
    .seq hls

/--
Removes leading whitespace from highlighted code.
-/
partial defmethod Highlighted.trimLeft (hl : Highlighted) : Highlighted :=
  match hl with
  | .text str => .text str.trimLeft
  | .token .. => hl
  | .span infos hl => .span infos hl.trimLeft
  | .tactics info startPos endPos hl => .tactics info startPos endPos hl.trimLeft
  | .point .. => hl
  | .seq hls => Id.run do
    let mut hls := hls
    repeat
      if h : hls.size > 0 then
        let first := hls[0].trimLeft
        if first.isEmpty then
          hls := hls.drop 1
        else
          hls := hls.set 0 first
          break
      else break
    .seq hls

/--
Removes leading and trailing whitespace from highlighted code.
-/
defmethod Highlighted.trim (hl : Highlighted) : Highlighted := hl.trimLeft.trimRight

defmethod Token.Kind.hover? (tok : Token.Kind) : HighlightHtmlM (Option Nat) :=
  match tok with
  | .const _n sig doc _ | .anonCtor _n sig doc =>
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
  | .withType t =>
    some <$> addHover {{ <code>{{t}}</code> }}
  | .sort (some doc) =>
    some <$> addHover {{<code class="docstring">{{doc}}</code>}}
  | .levelConst i =>
    some <$> addHover {{<code class="docstring">s!"The universe level {i}"</code>}}
  | .levelVar x =>
    some <$> addHover {{<code class="docstring">s!"The universe parameter {x}"</code>}}
  | .levelOp op =>
    let doc? :=
      match op with
      | "max" =>
        some "The maximum of two universes."
      | "imax" =>
        some "The impredicative maximum of two universes:\n\n * `imax u 0 = 0`\n * `imax u (v+1) = max u (v+1)`"
      | _ => none
    doc?.mapM fun doc =>
     addHover {{<code class="docstring">{{doc}}</code>}}
  | _ => pure none
where
  separatedDocs txt :=
    {{<span class="sep"/><code class="docstring">{{txt}}</code>}}

defmethod Lean.MessageSeverity.«class» : Lean.MessageSeverity → String
  | .information => "information"
  | .warning => "warning"
  | .error => "error"

defmethod Highlighted.Span.Kind.«class» : Highlighted.Span.Kind → String
  | .info => "info"
  | .warning => "warning"
  | .error => "error"

defmethod Token.Kind.«class» : Token.Kind → String
  | .var .. => "var"
  | .str .. => "literal string"
  | .sort .. => "sort"
  | .const .. => "const"
  | .option .. => "option"
  | .docComment => "doc-comment"
  | .keyword .. => "keyword"
  | .anonCtor .. => "unknown"
  | .unknown => "unknown"
  | .withType .. => "typed"
  | .levelConst .. => "level-const"
  | .levelVar .. => "level-var"
  | .levelOp .. => "level-op"

defmethod Token.Kind.data : Token.Kind → String
  | .const n _ _ _ | .anonCtor n _ _ => "const-" ++ toString n
  | .var ⟨v⟩ _ => "var-" ++ toString v
  | .option n _ _ => "option-" ++ toString n
  | .keyword _ (some occ) _ => "kw-occ-" ++ toString occ
  | .sort (some d) => s!"sort-{hash d}" -- equal docstrings as a proxy for the same operator
  | .levelVar x => s!"level-var-{x}"
  | .levelConst i => s!"level-const-{i}"
  | .levelOp op => s!"level-op-{op}"
  | _ => ""

defmethod Token.Kind.idAttr : Token.Kind → HighlightHtmlM (Array (String × String))
  | .const n _ _ true => do
    if let some id := (← read).definitionIds.find? n then
      pure #[("id", id)]
    else pure #[]
  | _ => pure #[]

defmethod Token.toHtml (tok : Token) : HighlightHtmlM Html := do
  let hoverId ← tok.kind.hover?
  let idAttr ← tok.kind.idAttr
  let hoverAttr := hoverId.map (fun i => #[("data-verso-hover", toString i)]) |>.getD #[]
  tok.kind.addLink {{
    <span class={{tok.kind.«class» ++ " token"}} data-binding={{tok.kind.data}} {{hoverAttr}} {{idAttr}}>{{tok.content}}</span>
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
                  <span for={{id}} class="goal-name">{{n.eraseMacroScopes.toString}}</span>
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
    out := out.push (f ⟨i, by get_elem_tactic⟩ arr[i])
  out

def _root_.Array.mapIndexedM [Monad m] (arr : Array α) (f : Fin arr.size → α → m β) : m (Array β) := do
  let mut out := #[]
  for h : i in [:arr.size] do
    out := out.push (← f ⟨i, by get_elem_tactic⟩ arr[i])
  pure out

partial defmethod Highlighted.toHtml : Highlighted → HighlightHtmlM Html
  | .token t => t.toHtml
  | .text str => pure {{<span class="inter-text">{{str}}</span>}}
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
      let visibleStates := (← options).visibleProofStates
      let checkedAttr :=
        if visibleStates.isVisible startPos endPos then #[("checked", "checked")] else #[]
      let id ← uniqueId (base := s!"tactic-state-{hash info}-{startPos}-{endPos}")
      pure {{
        <span class="tactic">
          <label for={{id}}>{{← toHtml hl}}</label>
          <input type="checkbox" class="tactic-toggle" id={{id}} {{checkedAttr}}></input>
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

defmethod Highlighted.blockHtml (contextName : String) (code : Highlighted) (trim : Bool := true) : HighlightHtmlM Html := do
  let code := if trim then code.trim else code
  pure {{ <code class="hl lean block" "data-lean-context"={{toString contextName}}> {{ ← code.toHtml }} </code> }}

defmethod Highlighted.inlineHtml (contextName : Option String) (code : Highlighted) (trim : Bool := true) : HighlightHtmlM Html := do
  let code := if trim then code.trim else code
  if let some ctx := contextName then
    pure {{ <code class="hl lean inline" "data-lean-context"={{toString ctx}}> {{ ← code.toHtml }} </code> }}
  else
    pure {{ <code class="hl lean inline"> {{ ← code.toHtml }} </code> }}

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
  padding: 0.5rem;
  z-index: 300;
  font-size: inherit;
}

.hl.lean .hover-info.messages {
  max-height: 10rem;
  overflow-y: auto;
  overflow-x: hidden;
  scrollbar-gutter: stable;
  padding: 0 0.5rem 0 0;
  display: block;
}

.hl.lean .hover-info code {
  white-space: pre-wrap;
}

.hl.lean .hover-info.messages > code {
  padding: 0.5rem;
  display: block;
  width: fit-content;
}

.hl.lean .hover-info.messages > code:only-child {
  margin: 0;
}

.hl.lean .hover-info.messages > code {
  margin: 0.1rem;
}

.hl.lean .hover-info.messages > code:not(:first-child) {
  margin-top: 0rem;
}

.hl.lean.block {
  display: block;
}

.hl.lean.inline {
  display: inline;
  white-space: pre-wrap;
}

.hl.lean .token {
  transition: all 0.25s; /* Slight fade for highlights */
}

@media (hover: hover) {
  .hl.lean .token.binding-hl, .hl.lean .literal.string:hover, .hl.lean .token.typed:hover {
    background-color: #eee;
    border-radius: 2px;
    transition: none;
  }
}


.hl.lean .has-info .token:not(.tactic-state):not(.tactic-state *), .hl.lean .has-info .inter-text:not(.tactic-state):not(.tactic-state *) {
  text-decoration-style: wavy;
  text-decoration-line: underline;
  text-decoration-thickness: from-font;
  text-decoration-skip-ink: none;
}

.hl.lean .has-info .hover-info {
  display: none;
  position: absolute;
  transform: translate(0.25rem, 0.3rem);
  border: 1px solid black;
  padding: 0.5rem;
  z-index: 400;
  text-align: left;
}

.hl.lean .has-info.error :not(.tactic-state):not(.tactic-state *){
  text-decoration-color: red;
}

@media (hover: hover) {
  .hl.lean .has-info.error:hover {
    background-color: #ffb3b3;
  }
}

.hl.lean .hover-info.messages > code.error {
  background-color: #e5e5e5;
  border-left: 0.2rem solid #ffb3b3;
}

.tippy-box[data-theme~='error'] .hl.lean .hover-info.messages > code.error {
  background: none;
  border: none;
}

.error pre {
    color: red;
}

.hl.lean .has-info.warning :not(.tactic-state):not(.tactic-state *) {
  text-decoration-color: var(--verso-warning-color);
}

@media (hover: hover) {
  .hl.lean .has-info.warning:hover {
    background-color:var(--verso-warning-color);
  }
}

.hl.lean .hover-info.messages > code.warning {
  background-color: var(--verso-warning-color);
}

.hl.lean .hover-info.messages > code.error {
  background-color: #e5e5e5;
  border-left: 0.2rem solid var(--verso-warning-color);
}

.tippy-box[data-theme~='warning'] .hl.lean .hover-info.messages > code.warning {
  background: none;
  border: none;
}


.hl.lean .has-info.info :not(.tactic-state):not(.tactic-state *) {
  text-decoration-color: blue;
}

@media (hover: hover) {
  .hl.lean .has-info.info:hover {
    background-color: #4777ff;
  }
}


.hl.lean .hover-info.messages > code.info {
  background-color: #e5e5e5;
  border-left: 0.2rem solid #4777ff;
}

.tippy-box[data-theme~='info'] .hl.lean .hover-info.messages > code.info {
  background: none;
  border: none;
}

.hl.lean div.docstring {
  font-family: sans-serif;
  white-space: normal;
  max-width: 40rem;
  width: max-content;
}

.hl.lean div.docstring > :last-child {
  margin-bottom: 0;
}

.hl.lean div.docstring > :first-child {
  margin-top: 0;
}

.hl.lean .hover-info .sep {
  display: block;
  width: auto;
  margin-left: 1rem;
  margin-right: 1rem;
  margin-top: 0.5rem;
  margin-bottom: 0.5rem;
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
  width: fit-content;
  border: 1px solid #888888;
  border-radius: 0.1rem;
  padding: 0.5rem;
  font-family: sans-serif;
  background-color: #ffffff;
}

.hl.lean.popup .tactic-state {
  position: static;
  display: block;
  width: auto;
  border: none;
  padding: 0.5rem;
  font-family: sans-serif;
  background-color: #ffffff;
}


.hl.lean .tactic {
  position: relative;
  display: inline-grid;
  grid-template-columns: 1fr;
  vertical-align: top;
}

.hl.lean .tactic-toggle:checked ~ .tactic-state {
  display: inline-block;
  vertical-align: top;
  grid-row: 2;
  justify-self: start;
}

.hl.lean .tactic > label {
  position: relative;
  grid-row: 1;
}

@media (hover: hover) {
  .hl.lean .tactic:has(.tactic-toggle:not(:checked)) > label:hover {
    background-color: #eeeeee;
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
  border-radius: 1rem;
  height: 0.25rem;
  vertical-align: middle;
  width: 0.6rem;
  margin-left: 0.1rem;
  margin-right: 0.1rem;
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
  margin-top: 1.5rem;
}

.hl.lean .tactic-state summary {
  margin-left: -0.5rem;
}

.hl.lean .tactic-state details {
  padding-left: 0.5rem;
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
  width: 1rem;
  height: 1rem;
  display: inline-block;
  background-color: black;
  content: ' ';
  transition: ease 0.2s;
  margin-right: 0.7rem;
  clip-path: polygon(100% 0, 0 0, 50% 100%);
  width: 0.6rem;
  height: 0.6rem;
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
  margin-left: 0.5rem;
  margin-top: 0.1rem;
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
  min-width: 1rem;
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
  border: 3px solid var(--verso-warning-color);
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
    let siteRoot = typeof __versoSiteRoot !== 'undefined' ? __versoSiteRoot : \"/\";
    let docsJson = siteRoot + \"-verso-docs.json\";
    fetch(docsJson).then((resp) => resp.json()).then((versoDocData) => {

      function hideParentTooltips(element) {
        let parent = element.parentElement;
        while (parent) {
          const tippyInstance = parent._tippy;
          if (tippyInstance) {
            tippyInstance.hide();
          }
          parent = parent.parentElement;
        }
      }



      const defaultTippyProps = {
        /* DEBUG -- remove the space: * /
        onHide(any) { return false; },
        trigger: \"click\",
        // */
        /* theme: \"lean\", */
        maxWidth: \"none\",
        appendTo: () => document.body,
        interactive: true,
        delay: [100, null],
        /* ignoreAttributes: true, */
        followCursor: 'initial',
        onShow(inst) {
          if (inst.reference.className == 'tactic') {

            const toggle = inst.reference.querySelector(\"input.tactic-toggle\");
            if (toggle && toggle.checked) {
              return false;
            }
            hideParentTooltips(inst.reference);
            //if (blockedByTippy(inst.reference)) { return false; }

          } else if (inst.reference.querySelector(\".hover-info\") || \"versoHover\" in inst.reference.dataset) {
            if (blockedByTactic(inst.reference)) { return false };
            if (blockedByTippy(inst.reference)) { return false; }
          } else { // Nothing to show here!
            return false;
          }
        },
        content (tgt) {
          const content = document.createElement(\"span\");
          if (tgt.className == 'tactic') {
            const state = tgt.querySelector(\".tactic-state\").cloneNode(true);
            state.style.display = \"block\";
            content.appendChild(state);
            content.style.display = \"block\";
            content.className = \"hl lean popup\";
          } else {
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
          }
          return content;
        }
      };


      document.querySelectorAll('.hl.lean .const.token, .hl.lean .keyword.token, .hl.lean .literal.token, .hl.lean .option.token, .hl.lean .var.token, .hl.lean .typed.token, .hl.lean .level-var, .hl.lean .level-const, .hl.lean .level-op, .hl.lean .sort').forEach(element => {
        element.setAttribute('data-tippy-theme', 'lean');
      });
      document.querySelectorAll('.hl.lean .has-info.warning').forEach(element => {
        element.setAttribute('data-tippy-theme', 'warning message');
      });
      document.querySelectorAll('.hl.lean .has-info.info').forEach(element => {
        element.setAttribute('data-tippy-theme', 'info message');
      });
      document.querySelectorAll('.hl.lean .has-info.error').forEach(element => {
        element.setAttribute('data-tippy-theme', 'error message');
      });
      document.querySelectorAll('.hl.lean .tactic').forEach(element => {
        element.setAttribute('data-tippy-theme', 'tactic');
      });
      let insts = tippy('.hl.lean .const.token, .hl.lean .keyword.token, .hl.lean .literal.token, .hl.lean .option.token, .hl.lean .var.token, .hl.lean .typed.token, .hl.lean .has-info, .hl.lean .tactic, .hl.lean .level-var, .hl.lean .level-const, .hl.lean .level-op, .hl.lean .sort', defaultTippyProps);
  });
}
"
