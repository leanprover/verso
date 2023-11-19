import LeanDoc.Genre.Blog.Site
import LeanDoc.Genre.Blog.Template

open LeanDoc.Genre.Blog Template
open LeanDoc Html

namespace LeanDoc.Genre.Blog

structure Theme where
  primaryTemplate : Template
  pageTemplate : Template
  postTemplate : Template
  archiveEntryTemplate : Template
  adHocTemplates : Array String → Option Template := fun _ => none

namespace Theme

def dirLinks : Dir Page → TemplateM (Array Html)
  | .pages subs => subs.mapM fun s => do
      let url ← mkLink [s.name]
      return {{<a href={{url}}>{{s.text.titleString}}</a>}}
  | .blog subs => subs.mapM fun s => do
      let url ← mkLink [(← currentConfig).postName s.date s.content.titleString]
      return {{<a href={{url}}>{{s.content.titleString}}</a>}}
where
  mkLink dest := do
    let dest' ← relative dest
    return String.join (dest'.map (· ++ "/"))

def topNav : Template := do
  let ⟨_, topPages⟩ := (← read).site
  return {{
    <nav class="top">
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
        <title>{{ (← param (α := String) "title") }}</title>
      </head>
      <body>
        {{ ← topNav }}
        <h1>{{ (← param "title") }}</h1>
        {{ (← param "content") }}
        {{ postList }}
      </body>
    </html>
  }}

def page : Template := param "content"

def post : Template := param "content"

def archiveEntry : Template := do
  let post : Post ← param "post"
  return #[{{
  <li>
    <a href={{← postName post}}>
    {{
    match post.date with
    | Date.mk y m d => {{<span class="date"> s!"{y}-{m}-{d}" </span>}}
    }}
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
