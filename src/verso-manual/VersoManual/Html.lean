/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Std.Data.HashSet
import Verso.Output.Html

import VersoManual.Basic

namespace Verso.Genre.Manual.Html
open Std (HashSet)
open Verso.Output Html

inductive Toc where
  | entry (title : Html) (path : Path) (id : String) (number : Bool) (children : Array Toc)
deriving Repr

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
        else path.map ("/" ++ ·) |>.toList |> String.join
      {{
        <li {{if !num then #[("class", "unnumbered")] else #[]}}>
          <a href=s!"{page}#{id}">{{title}}</a>
          {{if children.isEmpty || depth == some 1 then .empty
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

def page (toc : Array Toc) (textTitle : String) (htmlTitle : Html) (contents : Html) (extraCss : HashSet String) (extraJs : HashSet String) (extraStylesheets : List String := []) (extraScripts : List String := []) (extraJsFiles : Array String := #[]) : Html := {{
<html>
  <head>
    <meta charset="utf-8"/>
    <title>{{textTitle}}</title>
    <link rel="stylesheet" href="/book.css" />
    <script src="https://cdn.jsdelivr.net/npm/marked@11.1.1/marked.min.js" integrity="sha384-zbcZAIxlvJtNE3Dp5nxLXdXtXyxwOdnILY1TDPVmKFhl4r4nSUG1r8bcFXGVa4Te" crossorigin="anonymous"></script>
    {{extraJsFiles.map ({{<script src=s!"{·}"></script>}})}}
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
