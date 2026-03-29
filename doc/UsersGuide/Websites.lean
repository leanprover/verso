/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lean.DocString.Syntax
public import VersoManual
public meta import VersoManual.DB
meta import VersoBlog

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

{DB.dbDocstring Page}

{DB.dbDocstring Post}

Both feature the same set of extensions:

{DB.dbDocstring Blog.BlockExt}

{DB.dbDocstring Blog.InlineExt}

However, their metadata are different:

{DB.dbDocstring Page.Meta}

{DB.dbDocstring Post.Meta}

# Generating a Site
%%%
tag := "blogMain"
%%%

Blogs should have an executable that invokes {name Verso.Genre.Blog.blogMain}`blogMain` on the appropriate {ref "site-config"}[site and theme], forwarding on command-line arguments.
It is responsible for {ref "traversal"}[traversing] the site and generating the HTML.

{DB.dbDocstring Blog.blogMain}

# Configuring a Site
%%%
tag := "site-config"
%%%

The URL layout of a site is specified via a {name Blog.Site}`Site`:

{DB.dbDocstring Blog.Site}

{DB.dbDocstring Blog.Dir}

These are usually constructed using a small embedded configuration language.

A blog is rendered using a theme, which is a collection of templates.
Templates are monadic functions that construct {name Verso.Output.Html}`Html` from a set of dynamically-typed parameters.

{DB.dbDocstring Blog.Theme}

{DB.dbDocstring Blog.Template}

{DB.dbDocstring Blog.TemplateM}

{DB.dbDocstring Blog.Template.param}

{DB.dbDocstring Blog.Template.param?}

{DB.dbDocstring Blog.Template.builtinHeader}
