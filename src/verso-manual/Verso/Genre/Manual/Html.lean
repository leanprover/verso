/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Output.Html

import Verso.Genre.Manual.Basic

namespace Verso.Genre.Manual.Html
open Verso.Output Html

inductive Toc where
  | entry (title : Html) (path : Path) (id : String) (number : Bool) (children : Array Toc)

partial def Toc.html (depth : Option Nat) : Toc → Html
  | .entry title path id num children =>
    if depth = some 0 then .empty
    else
      let page := if path.isEmpty then "/" else path.map ("/" ++ ·) |>.toList |> String.join
      {{
        <li {{if !num then #[("class", "unnumbered")] else #[]}}>
          <a href=s!"{page}#{id}">{{title}}</a>
          {{if children.isEmpty then .empty
            else {{<ol> {{children.map (·.html (depth.map Nat.pred))}} </ol>}} }}
        </li>
      }}

def titlePage (title : Html) (authors : List String) (intro : Html) : Html := {{
  <div class="titlepage">
    <h1>{{title}}</h1>
    <div class="authors">
      {{authors.toArray.map ({{ <span class="author">{{Coe.coe ·}}</span> }})}}
    </div>
    {{intro}}
  </div>
}}

def page (toc : Array Toc) (textTitle : String) (htmlTitle : Html) (contents : Html) (extraCss : Lean.HashSet String) (extraJs : Lean.HashSet String) (extraStylesheets : List String := []) : Html := {{
<html>
  <head>
    <meta charset="utf-8"/>
    <title>{{textTitle}}</title>
    <link rel="stylesheet" href="/book.css" />
    {{extraStylesheets.map (fun url => {{<link rel="stylesheet" href={{url}}/> }})}}
    {{extraCss.toArray.map ({{<style>{{Html.text false ·}}</style>}})}}
    {{extraJs.toArray.map ({{<script>{{Html.text false ·}}</script>}})}}
  </head>
  <body>
    <div class="with-toc">
      <header>
        <h1>{{htmlTitle}}</h1>
        <div id="controls">
          <label for="toggle-toc" id="toggle-toc-click">"📖"</label>
        </div>
        <div id="print">
          <span>"🖨"</span>
        </div>
      </header>
      <nav id="toc">
        <input type="checkbox" id="toggle-toc" checked="checked"/>
        <ol>{{toc.map (·.html (some 3))}}</ol>
      </nav>
      <main>
        {{contents}}
      </main>
    </div>
  </body>
</html>
}}
