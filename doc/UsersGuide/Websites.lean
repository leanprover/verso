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

A blog is rendered using a theme, which is a collection of templates.
Templates are monadic functions that construct {name Verso.Output.Html}`Html` from a set of dynamically-typed parameters.

{docstring Blog.Theme}

{docstring Blog.Template}

{docstring Blog.TemplateM}

{docstring Blog.Template.param}

{docstring Blog.Template.param?}

{docstring Blog.Template.builtinHeader}
