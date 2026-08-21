/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.DocString.Syntax
import VersoManual
import VersoBlog

open Verso Genre Manual

open Verso.Genre.Blog (Page Post)

open InlineLean
open Verso.Doc

#doc (Manual) "Websites" =>
%%%
tag := "website"
htmlSplit := .never
%%%

Verso's website genre is a static site generator.
It contains two Verso {name}`Genre`s: {name}`Page` and {name}`Post`, which are identical except for their metadata:

{docstring Page}

{docstring Post}

Both feature the same set of extensions:

{docstring Blog.BlockExt}

{docstring Blog.InlineExt}

However, their metadata are different:

{docstring Page.Meta}

{docstring Post.Meta}

# Generating a Site
%%%
tag := "blogMain"
%%%

Blogs should have an executable that invokes `blogMain` on the appropriate {ref "site-config"}[site and theme], forwarding on command-line arguments.
It is responsible for {ref "traversal"}[traversing] the site and generating the HTML.

{docstring Blog.blogMain}

# Configuring a Site
%%%
tag := "site-config"
%%%

The URL layout of a site is specified via a {name Blog.Site}`Site`:

{docstring Blog.Site}

{docstring Blog.Dir}

These are usually constructed using a small embedded configuration language.
A page is written as its URL segment followed by the name of the document that it renders, further
pages are indented beneath a `/`, a blog is introduced by `with`, a directory of files that are
served verbatim by `static`, and a directory of {ref "rendered-html"}[rendered HTML content] by
`mount`:

```
def mySite : Site := site MySite.Front /
  static "static" ← "static_files"
  "about" MySite.About
  "blog" MySite.Blog with
    MySite.Blog.FirstPost
  "tutorials" MySite.Tutorials /
    mount "v1" ← "content/v1"
    mount "v0" ← "content/v0" with {showInNav := false}
```

The settings after `with` in a `mount` form are a {name Blog.MountSettings}`MountSettings`.

A blog is rendered using a theme, which is a collection of templates.
Templates are monadic functions that construct {name Verso.Output.Html}`Html` from a set of dynamically-typed parameters.

{docstring Blog.Theme}

A theme that is used to produce {ref "rendered-html"}[rendered HTML content] keeps its chrome in its
primary template, because the export renders the page template alone.

{docstring Blog.Template}

{docstring Blog.TemplateM}

{docstring Blog.Template.param}

{docstring Blog.Template.param?}

{docstring Blog.Template.builtinHeader}
