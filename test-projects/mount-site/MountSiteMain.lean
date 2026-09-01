/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoBlog
import MountSite

open Verso Genre Blog Site Syntax
open Verso.Output Html

/--
The site's own definitions of the custom properties that mounted content reads.

`builtinHeader` places a mount's own definitions ahead of everything else, and its own
`verso-vars.css` after those, so a property that this site defines takes this site's value and a
property that it does not define keeps the value that shipped with the content.
-/
private def siteVars : String := "
:root {
    --verso-text-color: #14213d;
    --verso-structure-color: #14213d;
    --verso-selected-color: #e5e5e5;
}

@media (prefers-color-scheme: dark) {
    :root {
        --verso-text-color: #edf2f4;
        --verso-structure-color: #edf2f4;
        --verso-selected-color: #2b2d42;
    }
}
"

/--
The site's own highlighted code and math, placed on a mounted page so that one document carries the
scripts of two Verso releases and each reaches only its own markup.
-/
def siteExtras : Html := {{
  <div class="site-extras">
    <code class="hl lean" data-lean-context="site">
      <span class="const token" id="site-token">
        <span class="hover-info">"The site's own hover."</span>
        "siteExample"
      </span>
    </code>
    <code class="math inline" id="site-math">r"\alpha + \beta"</code>
  </div>
}}

open Template Theme in
/--
The page template, which places `fragments.content` and `fragments.localNav` in the site's own
layout on a mounted page and the page's own content otherwise.
-/
def page : Template := do
  match (← param? (α := Html) "fragments.content") with
  | some content =>
    let localNav := (← param? (α := Html) "fragments.localNav").getD .empty
    return {{
      <article class="mounted">
        <h1>{{← param "title"}}</h1>
        {{siteExtras}}
        {{localNav}}
        {{content}}
      </article>
    }}
  | none =>
    return {{
      <article>
        <h1>{{← param "title"}}</h1>
        {{← param "content"}}
      </article>
    }}

open Template Theme in
/-- A template that replaces the page template for one mounted page. -/
def overriddenPage : Template := do
  let content := (← param? (α := Html) "fragments.content").getD .empty
  return {{
    <article class="mounted overridden">
      <p class="override-marker">"This page's template was replaced."</p>
      <h1>{{← param "title"}}</h1>
      {{content}}
    </article>
  }}

open Template Theme in
/--
The primary template. It invokes `builtinHeader` before defining the site's own custom properties,
so that the site's values override the ones that mounted content ships with.
-/
def primary : Template := do
  return {{
    <html>
      <head>
        <meta charset="utf-8"/>
        <meta name="viewport" content="width=device-width, initial-scale=1"/>
        <meta name="color-scheme" content="light dark"/>
        <link rel="icon" href="data:," />
        <title>{{← param (α := String) "title"}}</title>
        {{← builtinHeader}}
        <style>{{siteVars}}</style>
        <link rel="stylesheet" href="static/style.css"/>
      </head>
      <body>
        <header>{{← topNav}}</header>
        <main>{{← param "content"}}</main>
      </body>
    </html>
  }}

def theme : Theme :=
  { Theme.default with
    primaryTemplate := primary,
    pageTemplate := page }
  |>.override #["fixture", "guide", "first"] ⟨overriddenPage, id⟩

def mountSite : Site := site MountSite.Front /
  static "static" ← "test-projects/mount-site/static_files"
  mount "fixture" ← "test-projects/rendered-html-fixture"
  "guides" MountSite.Guides /
    mount "fixture-again" ← "test-projects/rendered-html-fixture"
  "tutorials" MountSite.Tutorials

/--
The directory that holds one directory of rendered HTML content per version of the tutorials.
-/
def tutorialContent : System.FilePath := "_out/tutorial-content"

/--
Discovery and ordering are the consumer's decisions, so they live here rather than in the format.

This is the shape that an assembly function follows: it runs in `IO`, so a target path that names
something other than a page fails here, with a clear message, rather than later.
-/
def addTutorials (into : Site) (under : List String) (root : System.FilePath) : IO Site := do
  unless ← root.pathExists do
    throw <| .userError <|
      s!"There is no directory at '{root}'. " ++
      "Run `lake exe tutorial-example-rendered-html` to produce the tutorials to mount."
  let mut result := into
  let mut names := #[]
  for entry in (← root.readDir) do
    if ← (entry.path / "verso-rendered-html.json").pathExists then
      names := names.push entry.fileName
  for name in names.qsort (· < ·) do
    result ← result.insertMount under name (root / name)
  return result

def main (args : List String) : IO UInt32 := do
  let mounted ← addTutorials mountSite ["tutorials"] tutorialContent
  blogMain theme mounted (options := args)
