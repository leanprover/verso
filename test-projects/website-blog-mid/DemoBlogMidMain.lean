
import VersoBlog.Site
import VersoBlog.Template

import DemoBlogMid.FrontPage
import DemoBlogMid.Posts
import DemoBlogMid.Post1
import DemoBlogMid.Post2

open Verso Genre Blog Site Syntax Template
open Lean (Html)

def dirLinks : Site → TemplateM (Array Html)
  | .page _ _ subs =>
    subs.filterMapM fun
      | .page name _id txt .. | .blog name _id txt .. =>
        if txt.metadata.map (·.showInNav) |>.getD true then
          pure <| some html%{<li><a href={s!"{name}/"}>{txt.titleString}</a></li>}
        else
          pure none
      | .static .. => pure none
  | .blog _ _ subs =>
    subs.mapM fun s => do
      let name ← s.postName'
      let url ← mkLink [name]
      return html%{<li><a href={url}>{s.contents.titleString}</a></li>}
  where
  mkLink dest := do
    let dest' ← relative dest
    return String.join (dest'.map (· ++ "/"))

def topNav (homeLink : Option String := none) : Template := do
    pure html%{
      <nav class="top" role="navigation">
        <ol>
          {homeLink.map (html%{<li class="home"><a href=".">s!"{·}"</a></li>}) |>.getD .empty}
          { ← dirLinks (← read).site }
        </ol>
      </nav>
    }

def primary : Template := do
  let postList :=
    match (← param? "posts") with
    | none => Html.empty
    | some html => html
  let catList :=
    match (← param? (α := Post.Categories) "categories") with
    | none => Html.empty
    | some ⟨#[]⟩ => Html.empty
    | some ⟨cats⟩ => html%{
        <div class="categories">
          <h2> "Categories" </h2>
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
        <!-- Stop favicon requests -->
        <link rel="shortcut icon" href="favicon.ico"/>
        <style>{":root { --justify-important: left; }"}</style>
        <title>{← param (α := String) "title"}</title>
        {← builtinHeader}
        <link rel="stylesheet" href="static/style.css"/>
      </head>
      <body>
        <header>
        {← topNav}
        </header>
        <main>
          {← param "content"}
          {postList}
          {catList}
        </main>
      </body>
    </html>
  }

def page : Template := do
  pure html%{
    <article>
      <h1>{← param "title"}</h1>
      {← param "content"}
    </article>
  }

def post : Template := do
  let catAddr ← do
    if let some p := (← param? "path") then
      pure <| fun slug => p ++ "/" ++ slug
    else pure <| fun slug => slug
  let title ← param "title"
  pure html%{
    { match (← param? "metadata") with
      | none => html%{<h1>{title}</h1>}
      | some md => html%{
        <small>{(md : Post.PartMetadata).date.toIso8601String}</small>
        <h1 class="post">{title}</h1>
      }
    }
    { match (← param? "metadata") with
       | none => Html.empty
       | some md => html%{
        <div class="metadata">
          { match (md : Post.PartMetadata).subtitle with
          | Option.some subtitle => html%{<div style="color:grey;"><big>html%{subtitle}</big></div>}
          | _ => Html.empty
          }
          {if md.categories.isEmpty then Html.empty
            else html%{
              <ul class="categories">
                {md.categories.toArray.map (fun cat => html%{<li><a href={s!"{catAddr cat.slug}"}>{cat.name}</a></li>})}
              </ul>
            }
          }
        </div>
       }
     }
    {← param "content"}
  }

def category : Template := do
  let category : Post.Category ← param "category"
  pure html%{
    <h1>{category.name}</h1>
  }

def archiveEntry : Template := do
  let post : BlogPost ← param "post"
  let target ← if let some p := (← param? "path") then
      pure <| p ++ "/" ++ (← post.postName')
    else post.postName'
  return html%{
    <li>
      <div class="post-list-item">
        <div class="post-list-item-desc">
          { match post.contents.metadata with
            | none => Html.empty
            | some md => html%{<div class="post-list-item-desc-date">{md.date.toIso8601String}</div>}
          }
          <a href={target} class="title">
            <div class="post-list-item-desc-title">{post.contents.titleString}</div>
          </a>
          { match post.contents.metadata >>= (·.subtitle) with
            | Option.some subtitle => html%{<div class="post-list-item-desc-subtitle">{subtitle}</div>}
            | _ => Html.empty
          }
        </div>
        <div class="post-list-item-img">
          { match post.contents.metadata >>= (·.featuredImage) with
            | Option.some imgpath => html%{<img src={imgpath}/>}
            | _ => Html.empty
          }
        </div>
      </div>
    </li>
  }

def customTheme : Theme where
  primaryTemplate := primary
  pageTemplate := page
  postTemplate := post
  categoryTemplate := category
  archiveEntryTemplate := archiveEntry

def blog : Site := site DemoBlogMid.FrontPage /
  static "static" ← "test-projects/website-blog-mid/static_files"
  "post" DemoBlogMid.Posts with
    DemoBlogMid.Post1
    DemoBlogMid.Post2

def main := blogMain customTheme blog
