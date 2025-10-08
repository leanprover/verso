/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Data.OpenDecl
import Lean.Data.Json
import Std.Data.HashMap
import SubVerso.Highlighting
import Verso.Doc
import Verso.Method
import Verso.Output.Html
import Verso.Instances.Deriving

open SubVerso.Highlighting
open Verso.Output Html
open Lean (Json ToJson FromJson Quote)
open Std (HashMap)

namespace SubVerso.Highlighting


/--
Serialize `Highlighted` code as a string.

Nothing should be assumed about the `String` output except that it can be passed to `hlFromExport`
to recover the original input.
-/
def hlToExport (hl: SubVerso.Highlighting.Highlighted) : String :=
  hl.exportCode.toJson.compress

/--
Recover the `Highlighted` data from its serialization.

Can only be expected to work on the output of `hlToExport`, likely to panic otherwise.
-/
def hlFromExport! (exportLit : String) : SubVerso.Highlighting.Highlighted :=
  match Lean.Json.parse exportLit with
  | .error e => panic! s!"Failed to parse Highlighted export data as JSON: {e}"
  | .ok v =>
    match SubVerso.Highlighting.ExportCode.fromJson? v with
    | .error e => panic! s!"Failed to deserialize Highlighted export data from parsed JSON: {e}"
    | .ok v' =>
      match v'.toHighlighted with
      | .error e => panic! s!"Failed to deserialize Highlighted data from export data: {e}"
      | .ok hl => hl


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
    | .text s | .unparsed s =>
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

structure CodeLink where
  /-- A very short description to show in hovers, like `"doc"` or `"src"` -/
  shortDescription : String
  /-- A longer description (at most one sentence) to describe the destination -/
  description : String
  /-- The actual link destination -/
  href : String
deriving Repr, DecidableEq, Ord

instance : ToJson CodeLink where
  toJson l := json%{"short": $l.shortDescription, "long": $l.description, "href": $l.href}

def CodeLink.inlineHtml (link : CodeLink) (text : Html) : Html :=
  {{<a href={{link.href}} title={{link.description}}>{{text}}</a>}}

def CodeLink.menuHtml (link : CodeLink) : Html :=
  {{<a href={{link.href}} title={{link.description}}>{{link.shortDescription}}</a>}}

def CodeLink.manyHtml (links : Array CodeLink) (text : Html) : Html :=
  if h : links.size = 1 then
    {{<a href={{links[0].href}} title={{links[0].description}}>{{text}}</a>}}
  else if h : links.size > 1 then
    let linkData := Json.arr (links.map ToJson.toJson) |>.compress
    {{<a href={{links[0].href}} title={{links[0].description}} data-verso-links={{linkData}}>{{text}}</a>}}
  else text

open Lean (Name FVarId Level) in
/--
Instructions for computing link targets for various code elements.

Each kind of link may have multiple destinations. The first is the default link, while the remainder
are considered alternates.
-/
structure LinkTargets (Ctxt : Type) where
  var : FVarId → Option Ctxt → Array CodeLink := fun _ _ => #[]
  sort : Level → Option Ctxt → Array CodeLink := fun _ _ => #[]
  const : Name → Option Ctxt → Array CodeLink := fun _ _ => #[]
  option : Name → Option Ctxt → Array CodeLink := fun _ _ => #[]
  keyword : Name → Option Ctxt → Array CodeLink := fun _ _ => #[]
  definition : Name → Option Ctxt → Array CodeLink := fun _ _ => #[]
  moduleName : Name → Option Ctxt → Array CodeLink := fun _ _ => #[]

def LinkTargets.augment (tgts1 tgts2 : LinkTargets g) : LinkTargets g where
  var fv ctxt := tgts1.var fv ctxt ++ tgts2.var fv ctxt
  sort l ctxt := tgts1.sort l ctxt ++ tgts2.sort l ctxt
  const n ctxt := tgts1.const n ctxt ++ tgts2.const n ctxt
  option o ctxt := tgts1.option o ctxt ++ tgts2.option o ctxt
  keyword kw ctxt := tgts1.keyword kw ctxt ++ tgts2.keyword kw ctxt
  definition x ctxt := tgts1.definition x ctxt ++ tgts2.definition x ctxt
  moduleName m ctxt := tgts1.moduleName m ctxt ++ tgts2.moduleName m ctxt

instance : Append (LinkTargets g) where
  append := LinkTargets.augment

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
  definitionsAsTargets : Bool := true

structure HighlightHtmlM.Context (g : Verso.Doc.Genre) where
  linkTargets : LinkTargets g.TraverseContext
  traverseContext : g.TraverseContext
  definitionIds : Lean.NameMap String
  options : HighlightHtmlM.Options

/--
Monad used to render highlighted Verso code to HTML.

The monad enables the following features:
1. Conveying options of type `HighlightHtmlM.Options` that govern the display of a particular piece of code.
2. Conveying document-wide configurations, in particular policies for hyperlinking identifiers.
3. De-duplicating hovers, which can greatly reduce the size of generated HTML.
-/
abbrev HighlightHtmlM g α := ReaderT (HighlightHtmlM.Context g) (StateT (State Html) Id) α

def addHover (content : Html) : HighlightHtmlM g Nat := modifyGet fun st =>
  let (hoverId, dedup) := st.dedup.insert content
  (hoverId, {st with dedup := dedup})

def uniqueId (base := "--verso-unique") : HighlightHtmlM g String := modifyGet fun st =>
  let (id, idSupply) := st.idSupply.unique (base := base)
  (id, {st with idSupply := idSupply})

def withCollapsedSubgoals (policy : HighlightHtmlM.CollapseGoals) (act : HighlightHtmlM g α) : HighlightHtmlM g α :=
  withReader (fun ctx => {ctx with options := {ctx.options with collapseGoals := policy} }) act

def withVisibleProofStates (policy : HighlightHtmlM.VisibleProofStates) (act : HighlightHtmlM g α) : HighlightHtmlM g α :=
  withReader (fun ctx => {ctx with options := {ctx.options with visibleProofStates := policy} }) act

def withDefinitionsAsTargets (saveIds : Bool) (act : HighlightHtmlM g α) : HighlightHtmlM g α :=
  withReader (fun ctx => {ctx with options := {ctx.options with definitionsAsTargets := saveIds} }) act

def linkTargets : HighlightHtmlM g (LinkTargets g.TraverseContext) := do
  return (← readThe (HighlightHtmlM.Context g)).linkTargets

def options : HighlightHtmlM g HighlightHtmlM.Options := do
  return (← readThe (HighlightHtmlM.Context g)).options

section
open Lean
open Verso.Output.Html

def constLink (constName : Name) (content : Html) (ctxt : Option g.TraverseContext := none) : HighlightHtmlM g Html := do
  return CodeLink.manyHtml ((← linkTargets).const constName ctxt) content

def optionLink (optionName : Name) (content : Html) (ctxt : Option g.TraverseContext := none) : HighlightHtmlM g Html := do
  return CodeLink.manyHtml ((← linkTargets).option optionName ctxt) content

def varLink (varName : FVarId) (content : Html) (ctxt : Option g.TraverseContext := none) : HighlightHtmlM g Html := do
  return CodeLink.manyHtml ((← linkTargets).var varName ctxt) content

def kwLink (kind : Name) (content : Html) (ctxt : Option g.TraverseContext := none) : HighlightHtmlM g Html := do
  return CodeLink.manyHtml ((← linkTargets).keyword kind ctxt) content

def defLink (defName : Name) (content : Html) (ctxt : Option g.TraverseContext := none) : HighlightHtmlM g Html := do
  return CodeLink.manyHtml ((← linkTargets).definition defName ctxt) content

def moduleNameLink (modName : Name) (content : Html) (ctxt : Option g.TraverseContext := none) : HighlightHtmlM g Html := do
  return CodeLink.manyHtml ((← linkTargets).moduleName modName ctxt) content
end

defmethod Token.Kind.addLink (tok : Token.Kind) (content : Html) : HighlightHtmlM g Html := do
  let ctxt := (← read).traverseContext
  match tok with
  | .const x _ _ false => constLink x content (some ctxt)
  | .const x _ _ true => defLink x content (some ctxt)
  | .option o .. => optionLink o content (some ctxt)
  | .var x .. => varLink x content (some ctxt)
  | .keyword (some k) .. => kwLink k content (some ctxt)
  | .moduleName m =>
    moduleNameLink m content (some ctxt)
  | _ => pure content

/--
Removes trailing whitespace from highlighted code.
-/
partial defmethod Highlighted.trimRight (hl : Highlighted) : Highlighted :=
  match hl with
  | .text str | .unparsed str => .text str.trimRight
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
  | .text str | .unparsed str => .text str.trimLeft
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

defmethod Token.Kind.hover? (tok : Token.Kind) : HighlightHtmlM g (Option Nat) :=
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
  | .info => "information"
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
  | .moduleName .. => "module-name"

defmethod Token.Kind.data : Token.Kind → String
  | .const n _ _ _ | .anonCtor n _ _ => "const-" ++ toString n
  | .var ⟨v⟩ _ => "var-" ++ toString v
  | .option n _ _ => "option-" ++ toString n
  | .keyword _ (some occ) _ => "kw-occ-" ++ toString occ
  | .sort (some d) => s!"sort-{hash d}" -- equal docstrings as a proxy for the same operator
  | .levelVar x => s!"level-var-{x}"
  | .levelConst i => s!"level-const-{i}"
  | .levelOp op => s!"level-op-{op}"
  | .moduleName m => s!"module-name-{m}"
  | _ => ""

defmethod Token.Kind.idAttr : Token.Kind → HighlightHtmlM g (Array (String × String))
  | .const n _ _ true => do
    if (← read).options.definitionsAsTargets then
      if let some id := (← read).definitionIds.find? n then
        return #[("id", id)]
    pure #[]
  | _ => pure #[]

defmethod Token.toHtml (tok : Token) : HighlightHtmlM g Html := do
  let hoverId ← tok.kind.hover?
  let idAttr ← tok.kind.idAttr
  let hoverAttr := hoverId.map (fun i => #[("data-verso-hover", toString i)]) |>.getD #[]
  tok.kind.addLink {{
    <span class={{tok.kind.«class» ++ " token"}} data-binding={{tok.kind.data}} {{hoverAttr}} {{idAttr}}>{{tok.content}}</span>
  }}

defmethod Highlighted.Goal.toHtml (exprHtml : expr → HighlightHtmlM g Html) (index : Nat) : Highlighted.Goal expr → HighlightHtmlM g Html
  | {name, goalPrefix, hypotheses, conclusion} => do
    let hypsHtml : Html ←
      if hypotheses.size = 0 then pure .empty
      else pure {{
        <span class="hypotheses">
          {{← hypotheses.mapM fun
              | ⟨names, t⟩ => do pure {{
                  <span class="hypothesis">
                    <span class="name">{{(← names.mapM (·.toHtml)).toList.intersperse {{" "}} }}</span><span class="colon">":"</span>
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
                  <span for={{id}} class="goal-name">{{n}}</span>
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

partial defmethod Highlighted.MessageContents.toHtml (expandTraces : List Lean.Name) (maxTraceDepth : Nat) (exprHtml : expr → HighlightHtmlM g Html) : Highlighted.MessageContents expr → HighlightHtmlM g Html
  | .text s => pure {{<span class="text">{{s}}</span>}}
  | .term e => do return {{<span class="highlighted">{{← exprHtml e}}</span>}}
  | .append xs => xs.foldlM (init := Html.empty) fun html m =>
      (html ++ ·) <$> m.toHtml expandTraces maxTraceDepth exprHtml
  | .trace cls msg children collapsed => do
    let msgHtml ← msg.toHtml expandTraces maxTraceDepth exprHtml
    let collapsed := collapsed && cls ∉ expandTraces
    let childHtml ←
      if maxTraceDepth = 0 then pure Html.empty
      else
        let cs ← children.mapM (·.toHtml expandTraces (maxTraceDepth - 1) exprHtml)
        pure {{<ul class="trace-children">{{cs.map ({{<li>{{·}}</li>}})}}</ul>}}
      if children.size > 0 then return {{
        <details class="trace" role="group" {{if collapsed then #[] else #[("open", "open")]}}><summary><span class="trace-class">s!"[{cls}]"</span> " " {{msgHtml}}</summary>{{childHtml}}</details>
      }} else return {{
        <span class="trace"><span class="trace-class">s!"[{cls}]"</span> " " {{msgHtml}}</span>
      }}

  | .goal g => g.toHtml exprHtml 0


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

partial defmethod Highlighted.toHtml : Highlighted → HighlightHtmlM g Html
  | .token t => t.toHtml
  | .text str | .unparsed str => pure {{<span class="inter-text">{{str}}</span>}}
  | .span infos hl =>
    if let some cls := spanClass infos then do
      pure {{<span class={{"has-info " ++ cls}}>
          <span class="hover-container">
            <span class={{"hover-info messages"}}>
              {{←  infos.mapM fun (s, info) => do return {{
                <code class={{"verso-message " ++ s.«class»}}>{{← info.toHtml [] 10 toHtml}}</code> }}
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
          <input type="checkbox" class="tactic-toggle" id={{id}} {{checkedAttr}}/>
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
  | .point s info => do
    let info ← info.toHtml [] 10 toHtml
    return {{
      <span class={{"verso-message " ++ s.«class»}}>{{info}}</span>
    }}
  | .seq hls => hls.mapM toHtml

defmethod Highlighted.blockHtml (contextName : String) (code : Highlighted) (trim : Bool := true) (htmlId : Option String := none) : HighlightHtmlM g Html := do
  let code := if trim then code.trim else code
  let idAttr := htmlId.map (fun x => #[("id", x)]) |>.getD #[]
  pure {{ <code class="hl lean block" "data-lean-context"={{toString contextName}} {{idAttr}}> {{ ← code.toHtml }} </code> }}

defmethod Highlighted.inlineHtml (contextName : Option String) (code : Highlighted) (trim : Bool := true) (htmlId : Option String := none) : HighlightHtmlM g Html := do
  let code := if trim then code.trim else code
  let idAttr := htmlId.map (fun x => #[("id", x)]) |>.getD #[]
  if let some ctx := contextName then
    pure {{ <code class="hl lean inline" "data-lean-context"={{toString ctx}} {{idAttr}}> {{ ← code.toHtml }} </code> }}
  else
    pure {{ <code class="hl lean inline" {{idAttr}}> {{ ← code.toHtml }} </code> }}

defmethod Highlighted.Message.toHtml (message : Highlighted.Message) (expandTraces : List Lean.Name) (maxTraceDepth : Nat := 10) : HighlightHtmlM g Html := do
  let contents ← message.contents.toHtml expandTraces maxTraceDepth (·.toHtml)
  return {{<span class=s!"verso-message">{{contents}}</span>}}

defmethod Highlighted.Message.blockHtml (message : Highlighted.Message) (summarize : Bool) (expandTraces : List Lean.Name := []) (maxTraceDepth : Nat := 10) : HighlightHtmlM g Html := do
  let wrap html :=
    if summarize then {{<details class=s!"lean-output {message.severity.class}"><summary>"Expand..."</summary><pre class="hl lean">{{html}}</pre></details>}}
    else {{<pre class=s!"hl lean lean-output {message.severity.class}">{{html}}</pre>}}
  wrap <$> message.toHtml expandTraces (maxTraceDepth := maxTraceDepth)


-- TODO CSS variables, and document them
def highlightingStyle : String := "

.hl.lean {
  white-space: pre;
  font-weight: normal;
  font-style: normal;
  font-size: inherit;
}

.hl.lean .keyword {
  color: var(--verso-code-keyword-color,);
  font-weight: var(--verso-code-keyword-weight, bold);
  font-style: var(--verso-code-keyword-style, normal);
  font-family: var(--verso-code-keyword-font-family,);
}

.hl.lean .const {
  color: var(--verso-code-const-color,);
  font-weight: var(--verso-code-const-weight, normal);
  font-style: var(--verso-code-const-style, normal);
  font-family: var(--verso-code-const-font-family,);
}

.hl.lean .var {
  color: var(--verso-code-var-color,);
  font-weight: var(--verso-code-var-weight, normal);
  font-style: var(--verso-code-var-style, italic);
  font-family: var(--verso-code-var-font-family,);

  position: relative;
}

.hl.lean .literal, .hl.lean .unknown {
  color: var(--verso-code-color,);
  font-weight: normal;
  font-style: normal;
  font-family: var(--verso-code-font-family,);
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
  background: none;
  color: black;
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

.hl.lean {
}

.hl.lean.block {
  display: block;
}

.hl.lean.inline {
  display: inline;
  white-space: pre-wrap;
}

.hl.lean * {
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

.error .verso-message, .error .verso-message .token, .error .verso-message label {
  color: var(--verso-error-color);
}

.error .verso-message .case-label:has(input[type=\"checkbox\"])::before {
  background-color: var(--verso-error-color) !important;
}

.hl.lean .has-info.warning :not(.tactic-state):not(.tactic-state *) {
  text-decoration-color: var(--verso-warning-indicator-color);
}

@media (hover: hover) {
  .hl.lean .has-info.warning:hover {
    background-color:var(--verso-warning-color);
  }
}

.hl.lean .hover-info.messages > code.warning {
  background-color: var(--verso-warning-color);
}

.lean-output {
  border-left: 0.2em solid transparent;
  padding: 0 0 0 0.5em;
  border-top-left-radius: 0;
  border-bottom-left-radius: 0;
}

.lean-output.error {
  border-color: var(--verso-error-indicator-color);
}

.lean-output.information {
  border-color: var(--verso-info-indicator-color);
}

.lean-output.warning {
  border-color: var(--verso-warning-indicator-color);
}

.hl.lean .hover-info.messages > code.error {
  background-color: #e5e5e5;
  border-left: 0.2rem solid var(--verso-warning-color);
}

.tippy-box[data-theme~='warning'] .hl.lean .hover-info.messages > code.warning {
  background: none;
  border: none;
}


.hl.lean .has-info.information :not(.tactic-state):not(.tactic-state *) {
  text-decoration-color: var(--verso-info-indicator-color, blue);
}

@media (hover: hover) {
  .hl.lean .has-info.information:hover {
    background-color: #4777ff;
  }
}


.hl.lean .hover-info.messages > code.information {
  background-color: #e5e5e5;
  border-left: 0.2rem solid #4777ff;
}

.tippy-box[data-theme~='info'] .hl.lean .hover-info.messages > code.information {
  background: none;
  border: none;
}

.hl.lean div.docstring {
  font-family: var(--verso-text-font-family, sans-serif);
  white-space: normal;
  max-width: calc(min(40rem, 90vw));
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
  font-family: var(--verso-code-font-family);
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
  display: inline;
  vertical-align: top;
  /* Without these, mobile Safari will start making font sizes inconsistent when its text size adjustment feature is triggered.*/
  -webkit-text-size-adjust: 100%;
  text-size-adjust: 100%;
}

.hl.lean .tactic:has(.tactic-toggle:checked) {
  display: inline-grid;
  grid-template-columns: 1fr;
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
  display: inline;
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
  /* These need to be em, not rem, to scale with the font */
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

/*
Some CSS frameworks customize details/summary in ways not compatible with Verso's output.
*/

.hl.lean details {
  display: block !important;
  margin: 0;
}

.hl.lean details summary {
  display: list-item !important;
  margin: 0;
}

.hl.lean details summary:focus {
  outline: none;
  outline-offset: none;
  color: inherit;
}

.hl.lean ul > li {
  margin-bottom: 0;
}

.hl.lean details summary::marker {
  display: inline !important;
}

.hl.lean details > summary:first-of-type {
  list-style-type: disclosure-closed;
  list-style-position: inside;
}

.hl.lean details[open] > summary:first-of-type {
  list-style-type: disclosure-open;
}

.hl.lean details summary::before, .hl.lean details summary::after {
  content: \"\" !important;
  background: none;
  display: none;
}

.hl.lean .tactic-state summary {
  /* These need to be em, not rem, to scale with the font */
  margin-left: -0.5em;
}

.hl.lean .tactic-state details {
  /* These need to be em, not rem, to scale with the font */
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
  display: inline-block;
  background-color: black;
  content: ' ';
  transition: ease 0.2s;
  margin-right: 0.7em;
  clip-path: polygon(100% 0, 0 0, 50% 100%);
  width: 0.6em;
  height: 0.6em;
  vertical-align: middle;
}

.hl.lean .case-label:has(input[type=\"checkbox\"]:not(:checked))::before {
  transform: rotate(-90deg);
}

.hl.lean .case-label:has(input[type=\"checkbox\"]) {

}

.hl.lean .case-label:has(input[type=\"checkbox\"]:checked) {

}


.hl.lean .labeled-case > :not(:first-child) {
  max-height: 0px;
  display: block;
  overflow: hidden;
  transition: max-height 0.1s ease-in;
  /* These need to be em, not rem, to scale with the font */
  margin-left: 0.5em;
  margin-top: 0.1em;
}

.hl.lean .labeled-case:has(.case-label input[type=\"checkbox\"]:checked) > :not(:first-child) {
  max-height: 100%;
}


.hl.lean .goal-name::before {
  font-style: normal;
  content: \"case \";
}

.hl.lean .goal-name {
  font-style: italic;
  font-family: var(--verso-code-font-family);
  color: inherit;
}

.hl.lean .hypotheses {
  display: table;
}

.hl.lean .hypothesis {
  display: table-row;
}

.hl.lean .hypothesis > * {
  display: table-cell;
}


.hl.lean .hypotheses .colon {
  text-align: center;
  /* This needs to be em, not rem, to scale with the font */
  min-width: 1em;
}

.hl.lean .hypotheses .name {
  text-align: right;
}

.hl.lean .hypotheses .name,
.hl.lean .hypotheses .type,
.hl.lean .conclusion .type {
  font-family: var(--verso-code-font-family);
}

.tippy-box {
  /* Without these, mobile Safari will start making font sizes inconsistent when its text size adjustment feature is triggered.*/
  -webkit-text-size-adjust: 100%;
  text-size-adjust: 100%;

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

.extra-doc-links {
  list-style-type: none;
  margin-left: 0;
  padding: 0;
}

.extra-doc-links > li {
  display: inline-block;
}

.extra-doc-links > li:not(:last-child)::after {
  content: '|';
  display: inline-block;
  margin: 0 0.25em;
}

.verso-message .trace {
  display: block;
}

.verso-message .trace > summary::marker {
  color: var(--verso-text-color);
}

.verso-message .trace-children {
  margin: 0;
  padding: 0;
}

.verso-message .trace-children > li {
  list-style-type: none;
  margin-left: 1.5em;
}

.verso-message .trace-children > li:not(:has(.trace)) {
  margin-left: 0;
}

.verso-message .trace-class {
  color: color-mix(in srgb, currentColor 70%, transparent);
  font-weight: bold;
  margin: 0;
  padding: 0;
}

.verso-message .text {
  white-space: pre-wrap;
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
            const extraLinks = tgt.parentElement.dataset['versoLinks'];
            if (extraLinks) {
              try {
                const extras = JSON.parse(extraLinks);
                const links = document.createElement('ul');
                links.className = 'extra-doc-links';
                extras.forEach((l) => {
                  const li = document.createElement('li');
                  li.innerHTML = \"<a href=\\\"\" + l['href'] + \"\\\" title=\\\"\" + l.long + \"\\\">\" + l.short + \"</a>\";
                  links.appendChild(li);
                });
                content.appendChild(links);
              } catch (error) {
                console.error(error);
              }
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
      document.querySelectorAll('.hl.lean .has-info.information').forEach(element => {
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
