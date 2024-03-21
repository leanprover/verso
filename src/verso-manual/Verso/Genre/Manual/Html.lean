/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Output.Html

namespace Verso.Genre.Manual.Html
open Verso.Output Html

inductive Toc where
  | entry (title : Html) (id : String) (number : Bool) (children : Array Toc)

partial def Toc.html (depth : Option Nat) : Toc → Html
  | .entry title id num children =>
    if depth = some 0 then .empty
    else
      {{
        <li>
          <a href=s!"#{id}" {{if !num then #[("class", "unnumbered")] else #[]}}>{{title}}</a>
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

def page (toc : Array Toc) (textTitle : String) (contents : Html) : Html := {{
<html>
  <head>
    <title>{{textTitle}}</title>
    <link rel="stylesheet" href="book.css" />
  </head>
  <body>
    <div class="with-toc">
      <header>
        <h1>{{textTitle}}</h1>
        <div id="controls">
          <label for="toggle-toc" id="toggle-toc-click">"📖"</label>
        </div>
        <div id="print">
          <span>"🖨"</span>
        </div>
      </header>
      <nav id="toc">
        <input type="checkbox" id="toggle-toc"/>
        <ol>{{toc.map (·.html (some 3))}}</ol>
      </nav>
      <main>
        {{contents}}
      </main>
    </div>
  </body>
</html>
}}
