/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoBlog
import DemoSite

open Verso Genre Blog Site Syntax

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do
    let postList :=
      match (← param? "posts") with
      | none => Html.empty
      | some html => {{ <h2> "Posts" </h2> }} ++ html
    let catList :=
      match (← param? (α := Post.Categories) "categories") with
      | none => Html.empty
      | some ⟨cats⟩ => {{
          <div class="category-directory">
            <h2> "Categories" </h2>
            <ul>
            {{ cats.map fun (target, cat) =>
              {{<li><a href={{target}}>{{Post.Category.name cat}}</a></li>}}
            }}
            </ul>
          </div>
        }}
    return {{
      <html>
        <head>
          <meta charset="utf-8"/>
          <meta name="viewport" content="width=device-width, initial-scale=1"/>
          <meta name="color-scheme" content="light dark"/>
          <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/sakura.css/css/sakura.css" type="text/css"/>
          <title>{{ (← param (α := String) "title") }} " — Verso "</title>
          {{← builtinHeader }}
          <link rel="stylesheet" href="static/style.css"/>
        </head>
        <body>
          <header>
            <div class="inner-wrap">
            <a class="logo" href="."><h1>"A Verso Site"</h1></a>
            {{ ← topNav }}
            </div>
          </header>
          <main>
            <div class="wrap">
              {{ (← param "content") }}
              {{ postList }}
              {{ catList }}
            </div>
          </main>
        </body>
      </html>
    }}
  }
  |>.override #[] ⟨do return {{<div class="frontpage"><h1>{{← param "title"}}</h1> {{← param "content"}}</div>}}, id⟩

def_literate_page litPage from LitLean in "examples/website-literate" as "Literate Lean page"

literate_page litPage' from DemoSite.LiteratePage in "." as "Literate Trees"

def_literate_post litPost from LitLean in "examples/website-literate" as "Literate Lean (post)" with {
  authors := ["An Author"]
  date := ⟨2025, 4, 4⟩
}

literate_post litPost' from DemoSite.LiteratePage in "." as "Literate Trees (post)" with {
  authors := ["An Author"]
  date := ⟨2025, 4, 4⟩
}



def demoSite : Site := site DemoSite.Front /
  static "static" ← "examples/website/static_files"
  "about" DemoSite.About
  "PHOAS" litPage
  "mod-doc-lit" litPage'
  "blog" DemoSite.Blog with
    litPost
    DemoSite.Blog.AnchorBased
    DemoSite.Blog.Subprojects
    DemoSite.Blog.Conditionals
    DemoSite.Blog.FirstPost


def linkTargets : Code.LinkTargets TraverseContext where
  const n _ := #[{shortDescription := "doc", description := s!"Documentation for {n}", href := s!"http://site.example/constlink/{n}"}]
  definition d _ := #[{shortDescription := "def", description := "Definition", href := s!"http://site.example/deflink/{d}"}]

def main := blogMain theme demoSite (linkTargets := linkTargets)
