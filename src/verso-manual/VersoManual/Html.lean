/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Std.Data.HashSet
import Verso.Output.Html

import VersoManual.Basic
import VersoManual.Html.Style

namespace Verso.Genre.Manual.Html
open Std (HashSet)
open Verso.Output Html
open Verso.Genre.Manual.Html.Css (pageStyleJs)

inductive Toc where
  | entry (title : Html) (path : Path) (id : String) (number : Option (Array Numbering)) (children : Array Toc)
deriving Repr

def Toc.title : Toc → Html
 | .entry title .. => title

def Toc.path : Toc → Path
 | .entry _ path .. => path

def Toc.id : Toc → Option String
 | .entry _ _ id .. => id

def Toc.sectionNum : Toc → Option (Array Numbering)
 | .entry _ _ _ num .. => num

def Toc.children : Toc → Array Toc
 | .entry _ _ _ _ children => children


/--
Convert a `Toc` to `HTML`.

The `depth` is a limit for the tree depth of the generated HTML (`none` for no limit).
-/
partial def Toc.html (depth : Option Nat) : Toc → Html
  | .entry title path id num children =>
    if depth = some 0 then .empty
    else
      let page :=
        if path.isEmpty then "/"
        else path.link
      let sectionNum :=
        match num with
        | none => {{<span class="unnumbered"></span>}}
        | some ns => {{<span class="number">{{sectionNumberString ns}}</span>" "}}
      {{
        <li>
          <a href=s!"{page}#{id}">{{sectionNum}}{{title}}</a>
          {{if children.isEmpty || depth == some 1 then .empty
            else {{<ol> {{children.map (·.html (depth.map Nat.pred))}} </ol>}} }}
        </li>
      }}

def Toc.navButtons (path : Path) (toc : Toc) : Html :=
  let (prev, parent, next) := findNav path toc
  {{
    <nav id="local-buttons">
      {{button prev {{<span class="arrow">"←"</span><span class="where">"Prev"</span>}} "prev"}}
      {{button parent {{<span class="arrow">"↑"</span><span class="where">"Up"</span>}} }}
      {{button next {{<span class="where">"Next"</span><span class="arrow">"→"</span>}} "next"}}
    </nav>
  }}

where
  button (toc : Option Toc) (label : Html) (rel : Option String := none) : Html :=
    if let some dest := toc then
      let relAttr := rel.map (fun r => #[("rel", r)]) |>.getD #[]
      {{
        <a class="local-button active" href={{dest.path.link dest.id}} {{relAttr}}>
          {{label}}
        </a>
      }}
    else
      {{<span class="local-button inactive">{{label}}</span>}}

  findNav (path : Path) (toc : Toc) : (Option Toc × Option Toc × Option Toc) := Id.run do
    let mut parent := none
    let mut here := toc
    let mut currentPath := #[]
    for lvl in path do
      currentPath := currentPath.push lvl
      parent := some here
      let children := here.children
      for h : i in [0:children.size] do
        if currentPath.isPrefixOf children[i].path then
          here := children[i]
          if here.path == path then
            let prev :=
              if i > 0 then
                have : i - 1 < children.size := by
                  let ⟨_, lt⟩ := h
                  simp only at lt
                  omega
                some children[i-1]
              else none
            let next := children[i+1]?
            return (prev, parent, next)
          break
    return (none, none, none)

def Toc.localHtml (path : Path) (toc : Toc) : Html := Id.run do
  let mut toc := toc
  let mut fallbackId : Nat := 0
  let rootId := "----bookRoot"
  let mut out : Html := splitTocElem true path.isEmpty rootId .empty (linkify #[] none toc.title) toc.children
  let mut currentPath := #[]
  for lvl in path do
    currentPath := currentPath.push lvl
    if let some nextStep := toc.children.find? (·.path == currentPath) then
      toc := nextStep
      let entryId ←
        if let some i := toc.id then pure i
        else
          fallbackId := fallbackId + 1
          pure s!"----header{fallbackId}"
      -- In the last position, when `path == currentPath`, the ToC should default to open
      out := out ++ splitTocElem false (path == currentPath) entryId (sectionNum toc.sectionNum) (linkify currentPath toc.id toc.title) toc.children
    else break
  {{<div class="split-tocs">{{out}}</div>}}
where
  splitTocElem (isTop thisPage : Bool) (chapterId : String) («section» : Html) (title : Html) (children : Array Toc) :=
    let toggleId := s!"--verso-manual-toc-{chapterId}"
    let «class» := if isTop then "split-toc book" else "split-toc"
    let checked := if thisPage then #[("checked", "checked")] else #[]
    {{
      <div class={{«class»}}>
        <div class="title">
          {{if children.isEmpty then {{
              <span class="no-toggle"/>
            }}
            else {{
              <label for={{toggleId}} class="toggle-split-toc">
                <input
                  type="checkbox"
                  class="toggle-split-toc"
                  id={{toggleId}}
                  {{checked}}/>
              </label>
            }}
          }}
          {{«section»}}
          <span class={{if thisPage && !isTop then "current" else ""}}>
            {{title}}
          </span>
        </div>
        {{if children.isEmpty then .empty
          else {{
            <table>
              {{children.map fun c =>
                let classes := String.intercalate " " <|
                  (if c.path.isPrefixOf path && !thisPage then
                    ["current"]
                   else []) ++
                  (if c.sectionNum.isSome then
                    ["numbered"]
                   else ["unnumbered"])

                {{<tr class={{classes}}>
                    <td class="num">
                      {{if let some ns := c.sectionNum then sectionNumberString ns
                        else .empty}}
                    </td>
                    <td>
                      {{linkify c.path c.id c.title}}
                    </td>
                  </tr>}}
              }}
            </table>
          }}
        }}
      </div>
    }}
  linkify (path : Path) (id : Option String) (html : Html) :=
    match html with
    | .tag "a" _ _ => html
    | other => {{<a href={{path.link id}}>{{other}}</a>}}
  sectionNum num :=
      match num with
      | none => {{<span class="unnumbered"></span>}}
      | some ns => {{<span class="number">{{sectionNumberString ns}}</span>" "}}

def titlePage (title : Html) (authors : List String) (intro : Html) : Html := {{
  <div class="titlepage">
    <h1>{{title}}</h1>
    <div class="authors">
      {{authors.toArray.map ({{ <span class="author">{{Coe.coe ·}}</span> }})}}
    </div>
    {{intro}}
  </div>
}}

def page
    (toc : Toc) (path : Path)
    (textTitle : String) (htmlTitle : Html) (contents : Html)
    (extraCss : HashSet String)
    (extraJs : HashSet String)
    (base : Option String := none)
    (logo : Option String := none)
    (repoLink : Option String := none)
    (issueLink : Option String := none)
    (extraStylesheets : List String := [])
    (extraJsFiles : Array String := #[]) : Html :=
  let relativeRoot :=
    base.getD (String.join <| "./" :: path.toList.map (fun _ => "../"))
  {{
    <html>
      <head>
        {{base.map ({{<base href={{·}}/>}}) |>.getD .empty}}
        <meta charset="utf-8"/>
        <title>{{textTitle}}</title>
        <link rel="stylesheet" href="/book.css" />
        <script>{{pageStyleJs}}</script>
        <script>s!"const __versoSiteRoot = \"{relativeRoot}\""</script>
        <script src="https://cdn.jsdelivr.net/npm/marked@11.1.1/marked.min.js" integrity="sha384-zbcZAIxlvJtNE3Dp5nxLXdXtXyxwOdnILY1TDPVmKFhl4r4nSUG1r8bcFXGVa4Te" crossorigin="anonymous"></script>
        {{extraJsFiles.map ({{<script src=s!"{·}"></script>}})}}
        {{extraStylesheets.map (fun url => {{<link rel="stylesheet" href={{url}}/> }})}}
        {{extraCss.toArray.map ({{<style>{{Html.text false ·}}</style>}})}}
        {{extraJs.toArray.map ({{<script>{{Html.text false ·}}</script>}})}}
      </head>
      <body>
        <label for="toggle-toc" id="toggle-toc-click">
          <span class="line line1"/>
          <span class="line line2"/>
          <span class="line line3"/>
        </label>
        <div class="with-toc">
          <nav id="toc">
            <input type="checkbox" id="toggle-toc" checked="checked"/>
            <div class="first">
              {{if let some url := logo then {{<img src={{url}} id="logo"/>}} else .empty }}
              {{toc.navButtons path}}
              {{toc.localHtml path}}
            </div>
            <div class="last">
              {{ if repoLink.isSome || issueLink.isSome then {{
                <ul id="meta-links">
                  {{if let some url := repoLink then
                    {{ <li><a href={{url}}>"Source Code"</a></li> }}
                    else .empty}}
                  {{if let some url := issueLink then
                    {{ <li><a href={{url}}>"Report Issues"</a></li> }}
                    else .empty}}
                </ul>
                }} else .empty }}
            </div>
          </nav>
          <main>
            {{contents}}
          </main>
        </div>
      </body>
    </html>
  }}

def relativize (path : Path) (html : Html) : Html :=
  html.visitM (m := ReaderT Path Id) (tag := rwTag) |>.run path
where
  urlAttr (name : String) : Bool := name ∈ ["href", "src", "data", "poster"]
  rwAttr (attr : String × String) : ReaderT Path Id (String × String) := do
    if urlAttr attr.fst && "/".isPrefixOf attr.snd then
      let path := (← read)
      pure { attr with
        snd := String.join (List.replicate path.size "../") ++ attr.snd.drop 1
      }
    else
      pure attr
  rwTag (tag : String) (attrs : Array (String × String)) (content : Html) : ReaderT Path Id (Option Html) := do
    if tag == "base" then pure none
    else pure <| some <| .tag tag (← attrs.mapM rwAttr) content
