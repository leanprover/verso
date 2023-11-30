import LeanDoc
import LeanDoc.Doc.Html
import LeanDoc.Genre

import BlogContents.Pages.Front
import BlogContents.Pages.Mission
import BlogContents.Pages.Blog
import BlogContents.Pages.Roadmap
import BlogContents.Pages.Team
import BlogContents.Pages.Contact
import BlogContents.Pages.Links
import BlogContents.Posts.AnExcellentPost
import BlogContents.Posts.AnotherPost

open LeanDoc.Genre Blog Theme Template
open LeanDoc.Genre.Blog.Site.Syntax
open LeanDoc Html

def theme : Theme := { Theme.default with
  primaryTemplate := do
    let postList :=
      match (← param? "posts") with
      | none => Html.empty
      | some html => {{ <h2> "Posts" </h2> }} ++ html
    return {{
      <html>
        <head>
          <meta charset="UTF-8"/>
          <title>{{ (← param (α := String) "title") }} " — Lean FRO"</title>
          <link rel="stylesheet" href="/static/style.css"/>
        </head>
        <body>
          <header>
            <div class="inner-wrap">
            <a class="logo" href="/"><img src="/static/lean_logo.svg"/></a>
            {{ ← topNav }}
            </div>
          </header>
          <div class="main" role="main">
            <div class="wrap">
              {{ (← param "title") }}
              {{ (← param "content") }}
              {{ postList }}
            </div>
          </div>
        </body>
      </html>
    }}
  }

def blog : Site := site BlogContents.Pages.Front /
  static "static" => "static"
  "about" BlogContents.Pages.Mission /
    "roadmap" BlogContents.Pages.Roadmap
  "blog" BlogContents.Pages.Blog /
    BlogContents.Posts.AnExcellentPost by "Some Author", "Co Author" on 2023-10-02
    BlogContents.Posts.AnotherPost     by "Some Author"              on 2023-10-15
  "team" BlogContents.Pages.Team
  "links" BlogContents.Pages.Links
  "contact" BlogContents.Pages.Contact
