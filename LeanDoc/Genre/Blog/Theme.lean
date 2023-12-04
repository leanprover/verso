import LeanDoc.Genre.Blog.Site
import LeanDoc.Genre.Blog.Template

open LeanDoc.Genre.Blog Template
open LeanDoc Html

namespace LeanDoc.Genre.Blog

structure Template.Override where
  template : Template
  params : Params → Params

structure Theme where
  primaryTemplate : Template
  pageTemplate : Template
  postTemplate : Template
  archiveEntryTemplate : Template
  /--
  Customize the rendering of a given path by replacing the
  template and providing additional parameters
  -/
  adHocTemplates : Array String → Option Template.Override := fun _ => none

def Theme.override (path : Array String) (override : Template.Override) (theme : Theme) : Theme :=
  {theme with
    adHocTemplates := fun p => if path = p then some override else theme.adHocTemplates p}

namespace Theme

def dirLinks : Dir Page → TemplateM (Array Html)
  | .pages subs =>
    subs.filterMapM fun
      | .page name _id txt .. =>
        pure <| some {{<li><a href={{"/" ++ name}}>{{txt.titleString}}</a></li>}}
      | .static .. => pure none
  | .blog subs =>
    subs.mapM fun s => do
      let url ← mkLink [(← currentConfig).postName s.date s.content.titleString]
      return {{<li><a href={{url}}>{{s.content.titleString}}</a></li>}}
where
  mkLink dest := do
    let dest' ← relative dest
    return String.join (dest'.map (· ++ "/"))

def topNav : Template := do
  let ⟨_, topPages⟩ := (← read).site
  return {{
    <nav class="top" role="navigation">
      <ol>
        {{ ← dirLinks topPages }}
      </ol>
    </nav>
  }}

namespace Default

def primary : Template := do
  let postList :=
    match (← param? "posts") with
    | none => Html.empty
    | some html => {{ <h2> "Posts" </h2> }} ++ html
  return {{
    <html>
      <head>
        <title>{{← param (α := String) "title"}}</title>
        <link rel="stylesheet" href="/static/style.css"/>
      </head>
      <body>
        {{← topNav}}
        {{← param "content"}}
        {{postList}}
      </body>
    </html>
  }}

def page : Template := do
  pure {{
    <h1>{{← param "title"}}</h1>
    {{← param "content"}}
  }}

def post : Template := page -- TODO author, date, etc

def archiveEntry : Template := do
  let post : Post ← param "post"
  return #[{{
  <li>
    <a href={{← postName post}}>
    {{
    match post.date with
    | Date.mk y m d => {{<span class="date"> s!"{y}-{m}-{d}" </span>}}
    }}
    " — "
    <span class="name">{{post.content.titleString}}</span>
    </a>
  </li>
}}]

end Default


open Default in
def default : Theme where
  primaryTemplate := primary
  pageTemplate := page
  postTemplate := post
  archiveEntryTemplate := archiveEntry
