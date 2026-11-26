/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoBlog
import DemoSite

open Verso Genre Blog Site Syntax
open Lean (Html)

open Output.Html.ContentSecurityPolicy

/--
An inline script in the theme.
-/
-- The content security policy must hash it, so the marker that it sets shows that theme scripts
-- still run.
--
-- With an external port, the script also loads `static/external-script.js` from
-- `http://localhost` on that port, as analytics snippets load their code. The browser tests serve
-- the site from `127.0.0.1`, which is a different origin, so that script runs only because the
-- policy lists the external origin as an extra script source. Its marker shows that extra sources
-- work.
def themeScript (externalPort : Option Port) : String :=
  "window.versoTestThemeInlineScript = true;\n" ++
  (externalPort.map fun port =>
    "(() => {\n" ++
    "  const script = document.createElement('script');\n" ++
    s!"  script.src = 'http://localhost:{port.number}/static/external-script.js';\n" ++
    "  document.head.append(script);\n" ++
    "})();\n").getD ""

open Output Html Template Theme in
def theme (externalPort : Option Port) : Theme := { Theme.default with
  jsFiles := #[("demo-theme.js", "window.versoTestThemeJsFile = true;", false)]
  primaryTemplate := do
    let postList :=
      match (← param? "posts") with
      | none => Html.empty
      | some html => html%{<h2>Posts</h2>} ++ html
    let catList :=
      match (← param? (α := Post.Categories) "categories") with
      | none => Html.empty
      | some ⟨cats⟩ => html%{
          <div class="category-directory">
            <h2>Categories</h2>
            <ul>
            { cats.map fun (target, cat) =>
              html%{<li><a href={target}>{Post.Category.name cat}</a></li>}
            }
            </ul>
          </div>
        }
    return html%{
      <html>
        <head>
          <meta charset="utf-8"/>
          <meta name="viewport" content="width=device-width, initial-scale=1"/>
          <meta name="color-scheme" content="light dark"/>
          <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/sakura.css/css/sakura.css" type="text/css"/>
          <title>{ (← param (α := String) "title") } — Verso </title>
          {← builtinHeader }
          <script>{Html.raw (themeScript externalPort)}</script>
          <link rel="stylesheet" href="static/style.css"/>
        </head>
        <body>
          <header>
            <div class="inner-wrap">
            <a class="logo" href="."><h1>A Verso Site</h1></a>
            { ← topNav }
            </div>
          </header>
          <main>
            <div class="wrap">
              { (← param "content") }
              { postList }
              { catList }
            </div>
          </main>
        </body>
      </html>
    }
  }
  |>.override #[] ⟨do return html%{<div class="frontpage"><h1>{← param "title"}</h1>{← param "content"}</div>}, id⟩

def_literate_page litPage from LitLean in "test-projects/website-literate" as "Literate Lean page"

literate_page litPage' from DemoSite.LiteratePage in "." as "Literate Trees"

def_literate_post litPost from LitLean in "test-projects/website-literate" as "Literate Lean (post)" with {
  authors := ["An Author"]
  date := ⟨2025, 4, 4⟩
}

literate_post litPost' from DemoSite.LiteratePage in "." as "Literate Trees (post)" with {
  authors := ["An Author"]
  date := ⟨2025, 4, 4⟩
}



def demoSite : Site := site DemoSite.Front /
  static "static" ← "test-projects/website/static_files"
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

-- `VERSO_TEST_EXTERNAL_SCRIPT_PORT` is the port of `http://localhost` from which the theme's inline
-- script loads `static/external-script.js`. The browser tests set it. Without it, the site doesn't
-- refer to an external origin.
def main (options : List String) : IO UInt32 := do
  let externalPort ←
    match ← IO.getEnv "VERSO_TEST_EXTERNAL_SCRIPT_PORT" with
    | none | some "" => pure none
    | some text =>
      let some n := text.toNat?
        | throw <| .userError s!"VERSO_TEST_EXTERNAL_SCRIPT_PORT: {text.quote} isn't a number."
      match Port.ofInt n with
      | .ok port => pure (some port)
      | .error e => throw <| .userError s!"VERSO_TEST_EXTERNAL_SCRIPT_PORT: {e}"
  let externalOrigin ← externalPort.mapM fun port => do
    match Host.ofString "localhost" with
    | .ok host => pure ({ scheme := some .http, host, port := some port } : Source)
    | .error e => throw <| .userError e
  blogMain (theme externalPort) demoSite (linkTargets := linkTargets) options
    (contentSecurityPolicy := { extraScriptSources := externalOrigin.toArray })
