
import VersoBlog.Site
import VersoBlog.Template

import DemoBlogMid.FrontPage
import DemoBlogMid.Posts
import DemoBlogMid.Post1
import DemoBlogMid.Post2

open Verso Genre Blog Site Syntax Template
open Lean (Html)

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

h1.post {
  font-family: var(--verso-structure-font-family);
  color: var(--verso-structure-color);
  line-height: 1.2;
  margin: 0.1em 0 0.1em;
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

ul.post-list {
  list-style-image: none;
  list-style-type: none;
  list-style: none;
  padding-left: 0px;
  margin-left: 0px;
  padding: 0px;
  margin: 0px;
}

.post-list li {
  list-style-image: none;
  list-style-type: none;
  list-style: none;
  padding-left: 0px;
  margin-left: 0px;
  padding: 0px;
  margin: 0px;
}

.post-list-item {
  display: flex;
  flex-flow: row;
  justify-content: space-between;
  align-items: center;
  grid-auto-columns: 1fr;
  gap: 0px;
  grid-template-columns: 1fr;
  grid-template-rows: auto auto;
  padding-bottom: 20px;
}

.post-list-item-img {
  height: 100%;
  max-width: none;
  align-self: auto;
  order: 0;
  flex: 0 1 auto;
  text-align: left;
}

.post-list-item-desc {
  max-width: 50%;
  display: block;
  padding-left: 0px;
  justify-content: flex-start;
  align-items: center;
}

.post-list-item-desc-date {
  color: grey;
  font-size: small;
}

.post-list-item-desc-title {
  font-size: big;
}

.post-list-item-desc-subtitle {
}
"#

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
        <link rel="shortcut icon" href="favicon.ico" />
        <style>{defaultBlogStyle}</style>
        <style>{":root { --justify-important: left; }"}</style>
        <title>{← param (α := String) "title"}</title>
        {← builtinHeader}
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
            | Option.some imgpath => html%{<img src={"./static/" ++ imgpath}/>}
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
