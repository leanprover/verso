/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Highlighting
import Verso.Method
import Verso.Output.Html

open SubVerso.Highlighting
open Verso.Output Html

namespace Verso.Code

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


defmethod Highlighted.Span.Kind.«class» : Highlighted.Span.Kind → String
  | .info => "info"
  | .warning => "warning"
  | .error => "error"

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

defmethod Token.toHtml (tok : Token) : Html := {{
  <span class={{tok.kind.«class» ++ " token"}} "data-binding"={{tok.kind.data}}>{{tok.content}}{{tok.kind.hover?.getD .empty}}</span>
}}

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
          {{if info.isEmpty then {{"All goals completed! 🐙"}} else info.mapIndexed (fun ⟨i, _⟩ x => x.toHtml toHtml i)}}
        </div>
      </span>
    }}
  | .point s info => {{<span class={{"message " ++ s.«class»}}>{{info}}</span>}}
  | .seq hls => hls.map toHtml

defmethod Highlighted.blockHtml (contextName : String) (code : Highlighted) : Html :=
  {{ <code class="hl lean block" "data-lean-context"={{toString contextName}}> {{ code.trim.toHtml }} </code> }}

defmethod Highlighted.inlineHtml (contextName : Option String) (code : Highlighted) : Html :=
  if let some ctx := contextName then
    {{ <code class="hl lean inline" "data-lean-context"={{toString ctx}}> {{ code.trim.toHtml }} </code> }}
  else
    {{ <code class="hl lean inline"> {{ code.trim.toHtml }} </code> }}

-- TODO CSS variables, and document them
def highlightingStyle : String := "

.hl.lean {
  white-space: pre;
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

.hl.lean .has-info .hover-info.messages {
  max-height: 10em;
  overflow-y: auto;
  overflow-x: hidden;
  padding: 0;
  background-color: #e5e5e5;
}

.hl.lean .hover-info code {
  white-space: pre;
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

.hl.lean .has-info > .hover-container > .hover-info > code.error {
  background-color: #ffb3b3;
}

.error pre {
    color: red;
}

.hl.lean .has-info.warning {
  text-decoration-color: yellow;
}

@media (hover: hover) {
  .hl.lean .has-info.warning:hover {
    background-color: yellow;
  }
}

.hl.lean .has-info .hover-info.messages > code.warning {
  background-color: yellow;
}

.hl.lean .has-info.info {
  text-decoration-color: blue;
}

@media (hover: hover) {
  .hl.lean .has-info.info:hover {
    background-color: #4777ff;
  }
}


.hl.lean .has-info .hover-info.messages > code.info {
  background-color: #4777ff;
}

.hl.lean div.docstring {
  font-family: sans-serif;
  white-space: normal;
  width: max-content;
  max-width: 40em;
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

.hl.lean .tactic {
  position: relative;
}

.hl.lean .tactic-toggle:checked ~ .tactic-state {
  display: block;
}

@media (hover: hover) {
  .hl.lean .tactic:hover > .tactic-toggle:not(:checked) ~ .tactic-state {
    display: block;
    position: absolute;
    left: 0;
    transform: translate(0.25rem, 0);
    z-index: 250;
  }
}

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

@media (hover: hover) {
  .hl.lean .tactic > label:hover::after {
    border: 1px solid #aaaaaa;
    background-color: #aaaaaa;
    transition: all 0.5s;
  }
}

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

.hl.lean .tactic-state .goal-name::before {
  font-style: normal;
  content: \"case \";
}

.hl.lean .tactic-state .goal-name {
  font-style: italic;
  font-family: monospace;
}

.hl.lean .tactic-state .hypotheses td.colon {
  text-align: center;
  min-width: 1em;
}

.hl.lean .tactic-state .hypotheses td.name {
  text-align: right;
}

.hl.lean .tactic-state .hypotheses td.name,
.hl.lean .tactic-state .hypotheses td.type,
.hl.lean .tactic-state .conclusion .type {
  font-family: monospace;
}

"

def highlightingJs : String :=
"window.onload = () => {
    for (const c of document.querySelectorAll(\".hl.lean .token\")) {
        if (c.dataset.binding != \"\") {
            c.addEventListener(\"mouseover\", (event) => {
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
}
"
