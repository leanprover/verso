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

def Theme.override (path : Array String) (override : Template.Override) (theme : Theme) : Theme :=
  {theme with
    adHocTemplates := fun p => if path = p then some override else theme.adHocTemplates p}

namespace Theme

def dirLinks : Site → TemplateM (Array Html)
  | .page _ _ subs =>
    subs.filterMapM fun
      | .page name _id txt .. | .blog name _id txt .. =>
        if txt.metadata.map (·.showInNav) |>.getD true then
          pure <| some {{<li><a href={{"/" ++ name}}>{{txt.titleString}}</a></li>}}
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
          {{homeLink.map ({{<li class="home"><a href="/">s!"{·}"</a></li>}}) |>.getD .empty}}
          {{ ← dirLinks (← read).site }}
        </ol>
      </nav>
    }}

namespace Default

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
        <link rel="stylesheet" href="https://unpkg.com/mvp.css"/>
        <title>{{← param (α := String) "title"}}</title>
        {{← builtinHeader}}
      </head>
      <body>
        {{← topNav}}
        {{← param "content"}}
        {{postList}}
        {{catList}}
      </body>
    </html>
  }}

def page : Template := do
  pure {{
    <h1>{{← param "title"}}</h1>
    {{← param "content"}}
  }}

def post : Template := do
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
                {{md.categories.toArray.map (fun cat => {{<li><a href=s!"../{cat.slug}">{{cat.name}}</a></li>}})}}
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
