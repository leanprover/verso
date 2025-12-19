/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoBlog.Site
import VersoBlog.Template

open Verso.Genre.Blog Template
open Verso Doc Output Html

namespace Verso.Genre.Blog

structure Template.Override where
  template : Template
  params : Params → Params

/--
A specification of how to render a site.
-/
structure Theme where
  /--
  The template used to render every page. It should construct an HTML value for the entire page,
  including the `<html>` element.

  In the `<head>` element, it should invoke `builtinHeader` to ensure that the required dependencies
  are present and that Verso-specific initialization is performed.

  In the body, it should check whether the parameter `"posts"` of type `Html` is present. If so, the
  page being rendered is a blog index, so it should place the parameter's value as a list of posts.
  If `"categories"` of type `Post.Categories` is present, it should render the contents as a
  category list.

  The parameter `"content"` of type `Html` contains the content of the page. It should be placed
  accordingly in the result.
  -/
  primaryTemplate : Template
  /--
  Pages are rendered using `pageTemplate`, with the result being passed in the `"content"` parameter
  to `primaryTemplate`. This template should use the `"title"` and `"content"` parameters to
  construct the contents of the page.
  -/
  pageTemplate : Template
  /--
  Blog posts are rendered using `pageTemplate`, with the result being passed in the `"content"`
  parameter to `primaryTemplate`. This template should use the `"title"` and `"content"` parameters
  to construct the contents of the post. Additionally, the `"metadata"` template of type
  `"Post.PartMetadata"` may be present; if so, it can be used to render the author, date, and
  categories of the post.
  -/
  postTemplate : Template
  /--
  The template used to summarize a blog post in a post archive. It receives the parameters `"post"`,
  which contains the post, and `"summary"`, which contains the HTML summary to display.
  -/
  archiveEntryTemplate : Template
  /--
  The template used to display a category at the top of a category's post list. It receives one
  parameter, `"category"`, which contains a `Post.Category`.
  -/
  categoryTemplate : Template
  /--
  Customize the rendering of a given path by replacing the
  template and providing additional parameters
  -/
  adHocTemplates : Array String → Option Template.Override := fun _ => none
  /--
  CSS files to be referenced in `<head>` and added to generated code.
  -/
  cssFiles : Array (String × String) := #[]
  /--
  JS files to be referenced in `<head>` or at the end of `<body>` and added to generated code.
  -/
  jsFiles : Array (String × String × Bool) := #[]

def Theme.override (path : Array String) (override : Template.Override) (theme : Theme) : Theme :=
  { theme with
    adHocTemplates := fun p => if path = p then some override else theme.adHocTemplates p }

namespace Theme

def dirLinks : Site → TemplateM (Array Html)
  | .page _ _ subs =>
    subs.filterMapM fun
      | .page name _id txt .. | .blog name _id txt .. =>
        if txt.metadata.map (·.showInNav) |>.getD true then
          pure <| some {{<li><a href={{name}}>{{txt.titleString}}</a></li>}}
        else
          pure none
      | .static .. => pure none
  | .blog _ _ subs =>
    subs.mapM fun s => do
      let name ← s.postName'
      let url ← mkLink [name]
      return {{<li><a href={{url}}>{{s.contents.titleString}}</a></li>}}
where
  mkLink dest := do
    let dest' ← relative dest
    return String.join (dest'.map (· ++ "/"))

def topNav (homeLink : Option String := none) : Template := do
    pure {{
      <nav class="top" role="navigation">
        <ol>
          {{homeLink.map ({{<li class="home"><a href=".">s!"{·}"</a></li>}}) |>.getD .empty}}
          {{ ← dirLinks (← read).site }}
        </ol>
      </nav>
    }}

namespace Default

private def defaultBlogStyle := r#"
:root {
  --max-width: 70ch;
  --spacing: 1.5rem;
  --color-accent: #0066cc;
  --color-border: #ddd;
}

* {
  box-sizing: border-box;
}

body {
  font-family: var(--verso-text-font-family);
  line-height: 1.6;
  color: var(--verso-text-color);
  background: #fff;
  margin: 0;
  padding: var(--spacing);
  max-width: var(--max-width);
  margin-inline: auto;
}

h1, h2, h3, h4, h5, h6 {
  font-family: var(--verso-structure-font-family);
  color: var(--verso-structure-color);
  line-height: 1.2;
  margin: 2em 0 0.5em;
}

h1 { font-size: 2rem; }
h2 { font-size: 1.5rem; }
h3 { font-size: 1.25rem; }

p, ul, ol, pre {
  margin: 0 0 1em;
}

a {
  color: var(--color-accent);
  text-decoration: none;
}

a:hover {
  text-decoration: underline;
}

code {
  font-family: var(--verso-code-font-family);
  color: var(--verso-code-color);
  background: #f4f4f4;
  padding: 0.2em 0.4em;
  border-radius: 3px;
  font-size: 0.9em;
}

pre {
  background: #f4f4f4;
  padding: 1em;
  border-radius: 5px;
  overflow-x: auto;
}

pre code {
  background: none;
  padding: 0;
}

blockquote {
  margin: 1em 0;
  padding-left: 1em;
  border-left: 3px solid var(--color-border);
  color: #666;
}

img {
  max-width: 100%;
  height: auto;
}

table {
  border-collapse: collapse;
  width: 100%;
  margin: 1em 0;
}

th, td {
  text-align: left;
  padding: 0.5em;
  border-bottom: 1px solid var(--color-border);
}

th {
  font-weight: 600;
  font-family: var(--verso-structure-font-family);
  color: var(--verso-structure-color);
}

nav.top {
  margin-bottom: 2rem;
  padding-bottom: 1rem;
  border-bottom: 1px solid var(--color-border);
}

nav.top ol {
  list-style: none;
  margin: 0;
  padding: 0;
  display: flex;
  gap: 1.5rem;
  flex-wrap: wrap;
}

nav.top li {
  margin: 0;
}

nav.top a {
  font-family: var(--verso-structure-font-family);
  color: var(--verso-structure-color);
  text-decoration: none;
  font-weight: 500;
}

nav.top a:hover {
  color: var(--color-accent);
  text-decoration: none;
}
"#

def primary : Template := do
  let postList :=
    match (← param? "posts") with
    | none => Html.empty
    | some html => {{ <h2> "Posts" </h2> }} ++ html
  let catList :=
    match (← param? (α := Post.Categories) "categories") with
    | none => Html.empty
    | some ⟨cats⟩ => {{
        <div class="categories">
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
        <!-- Stop favicon requests -->
        <link rel="icon" href="data:," />
        <style>{{defaultBlogStyle}}</style>
        <style>":root { --justify-important: left; }"</style>
        <title>{{← param (α := String) "title"}}</title>
        {{← builtinHeader}}
      </head>
      <body>
        <header>
        {{← topNav}}
        </header>
        <main>
          {{← param "content"}}
          {{postList}}
          {{catList}}
        </main>
      </body>
    </html>
  }}

def page : Template := do
  pure {{
    <article>
      <h1>{{← param "title"}}</h1>
      {{← param "content"}}
    </article>
  }}

def post : Template := do
  let catAddr ← do
    if let some p := (← param? "path") then
      pure <| fun slug => p ++ "/" ++ slug
    else pure <| fun slug => slug
  pure {{
    <h1>{{← param "title"}}</h1>
    {{ match (← param? "metadata") with
       | none => Html.empty
       | some md => {{
        <div class="metadata">
          <div class="authors">
            {{(md : Post.PartMetadata).authors.map ({{<span class="author">{{Html.text true ·}}</span>}}) |>.toArray}}
          </div>
          <div class="date">
            {{md.date.toIso8601String}}
          </div>
          {{if md.categories.isEmpty then Html.empty
            else {{
              <ul class="categories">
                {{md.categories.toArray.map (fun cat => {{<li><a href=s!"{catAddr cat.slug}">{{cat.name}}</a></li>}})}}
              </ul>
            }}
          }}
        </div>
       }}
     }}
    {{← param "content"}}
  }}

def category : Template := do
  let category : Post.Category ← param "category"
  pure {{
    <h1>{{category.name}}</h1>
  }}

def archiveEntry : Template := do
  let post : BlogPost ← param "post"
  let summary ← param "summary"
  let target ← if let some p := (← param? "path") then
      pure <| p ++ "/" ++ (← post.postName')
    else post.postName'
  let catAddr ← do
    if let some p := (← param? "path") then
      pure <| fun slug => p ++ "/" ++ slug
    else pure <| fun slug => slug

  return #[{{
    <li>
      <a href={{target}} class="title">
        <span class="name">{{post.contents.titleString}}</span>
      </a>
      {{ match post.contents.metadata with
         | none => Html.empty
         | some md => {{
          <div class="metadata">
            <div class="authors">
              {{(md : Post.PartMetadata).authors.map ({{<span class="author">{{Html.text true ·}}</span>}}) |>.toArray}}
            </div>
            <div class="date">
              {{md.date.toIso8601String}}
            </div>
            {{if md.categories.isEmpty then Html.empty
              else {{
                <ul class="categories">
                  {{md.categories.toArray.map (fun cat => {{<li><a href=s!"{catAddr cat.slug}">{{cat.name}}</a></li>}})}}
                </ul>
              }}
            }}
          </div>
         }}
       }}
      {{summary}}
      <a href={{target}} class="read-more">"Read more"</a>
    </li>
  }}]

end Default


open Default in
def default : Theme where
  primaryTemplate := primary
  pageTemplate := page
  postTemplate := post
  categoryTemplate := category
  archiveEntryTemplate := archiveEntry
