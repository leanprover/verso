/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean

import SubVerso.Highlighting

import Verso.Doc
import Verso.Doc.Html
import Verso.Genre.Blog.Basic
import Verso.Genre.Blog.Site
import Verso.Output.Html

open Lean (RBMap)

open Verso Doc Output Html
open Verso.Genre Blog
open SubVerso.Highlighting

private def next (xs : Array α) : Option (α × Array α) :=
  if _ : 0 < xs.size then
    some (xs[0], xs.extract 1 xs.size)
  else
    none

instance [Monad m] : MonadPath (HtmlT Post m) where
  currentPath := do
    let (_, ctxt, _) ← read
    pure ctxt.path

instance [Monad m] : MonadPath (HtmlT Page m) where
  currentPath := do
    let (_, ctxt, _) ← read
    pure ctxt.path

instance [Monad m] : MonadConfig (HtmlT Post m) where
  currentConfig := do
    let (_, ctxt, _) ← read
    pure ctxt.config

instance [Monad m] : MonadConfig (HtmlT Page m) where
  currentConfig := do
    let (_, ctxt, _) ← read
    pure ctxt.config

open HtmlT

defmethod Token.Kind.«class» : Token.Kind → String
  | .var _ _ => "var"
  | .str _ => "literal string"
  | .sort  => "sort"
  | .const _ _ _ => "const"
  | .option _ _ => "option"
  | .docComment => "doc-comment"
  | .keyword _ _ _ => "keyword"
  | .unknown => "unknown"

defmethod Token.Kind.data : Token.Kind → String
  | .const n _ _ => "const-" ++ toString n
  | .var ⟨v⟩ _ => "var-" ++ toString v
  | .option n _ => "option-" ++ toString n
  | .keyword _ (some occ) _ => "kw-occ-" ++ toString occ
  | _ => ""


def hover (content : Html) : Html := {{
  <span class="hover-container"><span class="hover-info"> {{ content }} </span></span>
}}

defmethod Token.Kind.hover? : (tok : Token.Kind) → Option Html
  | .const _n sig doc =>
    let docs := match doc with
      | none => .empty
      | some txt => {{<span class="sep"/><code class="docstring">{{txt}}</code>}}
    some <| hover {{ <code>{{sig}}</code> {{docs}} }}
  | .option n doc =>
    let docs := match doc with
      | none => .empty
      | some txt => {{<span class="sep"/><code class="docstring">{{txt}}</code>}}
    some <| hover {{ <code>{{toString n}}</code> {{docs}} }}
  | .keyword _ _ none => none
  | .keyword _ _ (some doc) => some <| hover {{<code class="docstring">{{doc}}</code>}}
  | .var _ type =>
    some <| hover {{ <code>{{type}}</code> }}
  | .str s =>
    some <| hover {{ <code><span class="literal string">{{s.quote}}</span>" : String"</code>}}
  | _ => none


defmethod Token.toHtml (tok : Token) : Html := {{
  <span class={{tok.kind.«class» ++ " token"}} "data-binding"={{tok.kind.data}}>{{tok.content}}{{tok.kind.hover?.getD .empty}}</span>
}}


defmethod Highlighted.Span.Kind.«class» : Highlighted.Span.Kind → String
  | .info => "info"
  | .warning => "warning"
  | .error => "error"

defmethod Highlighted.Goal.toHtml (exprHtml : expr → Html) (index : Nat) : Highlighted.Goal expr → Html
  | {name, goalPrefix, hypotheses, conclusion} =>
    let hypsHtml : Html :=
      if hypotheses.size = 0 then .empty
      else {{
        <table class="hypotheses">
          {{hypotheses.map fun
              | (x, k, t) => {{
                  <tr class="hypothesis">
                    <td class="name">{{Token.toHtml ⟨k, x.toString⟩}}</td><td class="colon">":"</td>
                    <td class="type">{{exprHtml t}}</td>
                  </tr>
                }}
          }}
        </table>
      }}
    let conclHtml := {{
        <span class="conclusion">
          <span class="prefix">{{goalPrefix}}</span><span class="type">{{exprHtml conclusion}}</span>
        </span>
      }}
    {{
      <div class="goal">
        {{ match name with
          | none => {{
             {{hypsHtml}}
             {{conclHtml}}
            }}
          | some n => {{
              <details {{if index = 0 then #[("open", "open")] else #[]}}>
                <summary><span class="goal-name">{{n.toString}}</span></summary>
               {{hypsHtml}}
               {{conclHtml}}
              </details>
            }}
        }}
      </div>
    }}

def _root_.Array.mapIndexed (arr : Array α) (f : Fin arr.size → α → β) : Array β :=
  let rec go (acc : Array β) (i : Nat) :=
    if h : i < arr.size then
      go (acc.push (f ⟨i, h⟩ arr[i])) (i + 1)
    else acc
  termination_by arr.size - i
  go #[] 0

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

partial defmethod Highlighted.toHtml : Highlighted → Html
  | .token t => t.toHtml
  | .text str => str
  | .span infos hl =>
    if let some cls := spanClass infos then
      {{<span class={{"has-info " ++ cls}}>
          <span class="hover-container">
            <span class={{"hover-info messages"}}>
              {{ infos.map fun (s, info) => {{
                <code class={{"message " ++ s.«class»}}>{{info}}</code> }}
              }}
            </span>
          </span>
          {{toHtml hl}}
        </span>
      }}
    else
      panic! "No highlights!"
      --toHtml hl
  | .tactics info startPos endPos hl =>
    let id := s!"tactic-state-{hash info}-{startPos}-{endPos}"
    {{
      <span class="tactic">
        <label «for»={{id}}>{{toHtml hl}}</label>
        <input type="checkbox" class="tactic-toggle" id={{id}}></input>
        <div class="tactic-state">
          {{if info.isEmpty then {{"All goals completed! 🐙"}} else info.mapIndexed (fun ⟨i, _⟩ x => x.toHtml Highlighted.toHtml i)}}
        </div>
      </span>
    }}
  | .point s info => {{<span class={{"message " ++ s.«class»}}>{{info}}</span>}}
  | .seq hls => hls.map toHtml

defmethod LexedText.toHtml (text : LexedText) : Html :=
  text.content.map fun
    | (none, txt) => (txt : Html)
    | (some cls, txt) => {{ <span class={{cls}}>{{txt}}</span>}}

def blockHtml (g : Genre) (go : Block g → HtmlT g IO Html) : Blog.BlockExt → Array (Block g) → HtmlT g IO Html
  | .lexedText content, _contents => do
    pure {{ <pre class=s!"lexed {content.name}"> {{ content.toHtml }} </pre> }}
  | .highlightedCode contextName hls, _contents => do
    pure {{ <code class="hl lean block" "data-lean-context"={{toString contextName}}> {{ hls.trim.toHtml }} </code> }}
  | .htmlDetails classes summary, contents => do
    pure {{ <details class={{classes}}><summary>{{summary}}</summary> {{← contents.mapM go}}</details>}}
  | .htmlWrapper name attrs, contents => do
    Html.tag name attrs <$> contents.mapM go
  | .htmlDiv classes, contents => do
    pure {{ <div class={{classes}}> {{← contents.mapM go}} </div> }}
  | .blob html, _ => pure html

def inlineHtml (g : Genre) [MonadConfig (HtmlT g IO)] [MonadPath (HtmlT g IO)]
    (stateEq : g.TraverseState = Blog.TraverseState)
    (go : Inline g → HtmlT g IO Html) : Blog.InlineExt → Array (Inline g) → HtmlT g IO Html
  | .highlightedCode contextName hls, _contents => do
    pure {{ <code class="hl lean inline" "data-lean-context"={{toString contextName}}> {{ hls.trim.toHtml }} </code> }}
  | .customHighlight hls, _contents => do
    pure {{ <code class="hl lean inline"> {{ hls.trim.toHtml }} </code> }}
  | .label x, contents => do
    let contentHtml ← contents.mapM go
    let st ← stateEq ▸ state
    let some tgt := st.targets.find? x
      | panic! "No label for {x}"
    pure {{ <span id={{tgt.htmlId}}> {{ contentHtml }} </span>}}
  | .ref x, contents => do
    let st ← stateEq ▸ state
    match st.targets.find? x with
    | none =>
      HtmlT.logError "Can't find target {x}"
      pure {{<strong class="internal-error">s!"Can't find target {x}"</strong>}}
    | some tgt =>
      let addr := s!"{String.join ((← relative tgt.path).intersperse "/")}#{tgt.htmlId}"
      go <| .link contents addr
  | .pageref x, contents => do
    let st ← stateEq ▸ state
    match st.pageIds.find? x with
    | none =>
      HtmlT.logError "Can't find target {x}"
      pure {{<strong class="internal-error">s!"Can't find target {x}"</strong>}}
    | some meta =>
      let addr := String.join ((← relative meta.path).intersperse "/")
      go <| .link contents addr
  | .htmlSpan classes, contents => do
    pure {{ <span class={{classes}}> {{← contents.mapM go}} </span> }}
  | .blob html, _ => pure html

def blogGenreHtml (g : Genre) [MonadConfig (HtmlT g IO)] [MonadPath (HtmlT g IO)]
    (eq1 : g.Block = Blog.BlockExt) (eq2 : g.Inline = Blog.InlineExt) (eq3 : g.TraverseState = Blog.TraverseState)
    (partMeta : (Part g → Array (String × String) → HtmlT g IO Html) → g.PartMetadata → Part g → HtmlT g IO Html) : GenreHtml g IO where
  part f m := partMeta f m
  block := eq1 ▸ blockHtml g
  inline := eq2 ▸ inlineHtml g eq3

instance : GenreHtml Page IO := blogGenreHtml Page rfl rfl rfl fun go _metadata part => go part #[]
instance : GenreHtml Post IO := blogGenreHtml Post rfl rfl rfl fun go _metadata part => go part #[]

namespace Verso.Genre.Blog.Template

structure Params.Val where
  value : Dynamic
  fallback : Array Dynamic

namespace Params.Val

def get? [TypeName α] (value : Val) : Option α :=
  value.value.get? α <|> do
    for v in value.fallback do
      if let some x := v.get? α then return x
    none

def getD [TypeName α] (value : Val) (default : α) : α :=
  value.get? |>.getD default

end Params.Val

deriving instance TypeName for String


instance : Coe String Template.Params.Val where
  coe str := ⟨.mk str, #[.mk <| Html.text true str]⟩

instance : Coe Html Template.Params.Val where
  coe
   | .text true str => ↑str
   | other => ⟨.mk other, #[]⟩


def Params := RBMap String Params.Val compare

instance : EmptyCollection Params := inferInstanceAs <| EmptyCollection (RBMap _ _ _)

namespace Params

def ofList (params : List (String × Val)) : Params :=
  Lean.RBMap.ofList params

def toList (params : Params) : List (String × Val) :=
  Lean.RBMap.toList params

def insert (params : Params) (key : String) (val : Val) : Params :=
  Lean.RBMap.insert params key val

def erase (params : Params) (key : String) : Params :=
  Lean.RBMap.erase params key


end Params

inductive Error where
  | missingParam (param : String)
  | wrongParamType (param : String) (type : Lean.Name)

structure Context where
  site : Site
  config : Config
  path : List String
  params : Params
  builtInStyles : Lean.HashSet String
  builtInScripts : Lean.HashSet String

end Template

abbrev TemplateM (α : Type) : Type := ReaderT Template.Context (Except Template.Error) α

abbrev Template := TemplateM Html

instance : MonadPath TemplateM where
  currentPath := Template.Context.path <$> read

instance : MonadConfig TemplateM where
  currentConfig := Template.Context.config <$> read

namespace Template

def param? [TypeName α] (key : String) : TemplateM (Option α) := do
  match (← read).params.find? key with
  | none => return none
  | some val =>
    if let some v := val.get? (α := α) then return (some v)
    else throw <| .wrongParamType key (TypeName.typeName α)


def param [TypeName α] (key : String) : TemplateM α := do
  match (← read).params.find? key with
  | none => throw <| .missingParam key
  | some val =>
    if let some v := val.get? (α := α) then return v
    else throw <| .wrongParamType key (TypeName.typeName α)

def builtinHeader : TemplateM Html := do
  let mut out := .empty
  for style in (← read).builtInStyles do
    out := out ++ {{<style>"\n"{{.text false style}}"\n"</style>"\n"}}
  for script in (← read).builtInScripts do
    out := out ++ {{<script>"\n"{{.text false script}}"\n"</script>"\n"}}
  out := out ++ {{
    <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css" integrity="sha384-n8MVd4RsNIU0tAv4ct0nTaAbDJwPJzDEaqSD1odI+WdtXRGWt2kTvGFasHpSy3SV" crossorigin="anonymous"/>
    <script defer="defer" src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.js" integrity="sha384-XjKyOOlGwcjNTAIQHIpgOno0Hl1YQqzUOEleOLALmuqehneUG+vnGctmUb0ZY0l8" crossorigin="anonymous"></script>
    <script src="https://cdn.jsdelivr.net/npm/marked@11.1.1/marked.min.js" integrity="sha384-zbcZAIxlvJtNE3Dp5nxLXdXtXyxwOdnILY1TDPVmKFhl4r4nSUG1r8bcFXGVa4Te" crossorigin="anonymous"></script>
  }}

  pure out

namespace Params

end Params
