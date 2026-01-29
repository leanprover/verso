/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual
import UsersGuide.Markup
import UsersGuide.Websites
import UsersGuide.Manuals
import UsersGuide.Elab
import UsersGuide.Extensions
import UsersGuide.Output
import UsersGuide.Releases

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Writing Documentation in Lean with Verso" =>

%%%
shortTitle := "Documentation with Verso"
authors := ["David Thrane Christiansen"]
%%%

:::paragraph
Verso is a tool for writing about Lean.
Or, rather, it is a framework for constructing such tools, together with concrete tools that use this framework.
Technical writing can take many forms, including but not limited to:
 * Reference manuals
 * Tutorials
 * Web pages
 * Academic papers
:::

All of these genres have common concerns, such as displaying Lean code, including tests to prevent bit-rot of the text, and linking to other resources.
However, they are also very different.
Some have a very linear structure, while others combine date-based content with an unordered set of pages.
Some should generate highly interactive output, while others should generate PDFs that can be turned into published papers books.

Verso consists of the following components:

: Markup language

  Verso's {ref "verso-markup"}[markup language] is a simplified variant of Markdown.
  It is also an alternative concrete syntax for Lean itself, so Verso documents are just Lean files.
  Just as TeX, Sphinx, and Scribble allow their languages to be extended using their own programming languages, Verso's markup language is extensible.
  Define a Lean function at the top of a file, and use it in the text of that very same file.

: Extensible document structure

  All Verso documents can contain a set of {ref "elaboration"}[common elements], such as paragraphs, emphasized text, or images.
  They also share a hierarchical structure of sections and subsections.
  These types are extensible by individual genres.

: Elaboration and rendering framework

  Verso provides a shared paradigm for converting text written by an author into readable output.
  Different genres will produce different output formats, but they don't need to reinvent the wheel in order to resolve cross-references, and they can benefit from shared libraries for producing output in various formats.

: Cross-reference management

  Verso includes a common paradigm for representing the documented items, and a format for sharing cross-reference databases between genres that emit HTML, which enables links and cross-references to be automatically inserted and maintained.

: Lean rendering

  Verso includes facilities for elaborating and displaying Lean code in documents.
  In HTML output, this code is rendered with toggleable proof states, hovers, and hyperlinks.
  It's also highlighted accurately, which is impossible with regexp-based highlighting due to Lean's syntactic extensibility.

  The [`SubVerso`](https://github.com/leanprover/subverso) helper library allows Verso documents to process Lean code written in any version of Lean, starting with `4.0.0`.
  This makes it possible to write a document that compares and contrasts versions, or to decouple upgrades to the Lean version used in a project from the Lean version used in the document that describes it.

: Utility libraries

  Verso includes utility libraries that can be used by genres to provide features such as full-text search of HTML content.
  These libraries have no additional build-time dependencies, avoiding the complications of staying up to date with multiple library ecosystems at once.



# Genres
%%%
tag := "genres"
%%%


:::paragraph
Documentation comes in many forms, and no one system is suitable for representing all of them.
The needs of software documentation writers are not the same as the needs of textbook authors, researchers writing papers, bloggers, or poets.
Thus, Verso supports multiple {deftech}_genres_, each of which consists of:

 * A global view of a document's structure, whether it be a document with subsections, a collection of interrelated documents such as a web site, or a single file of text
 * A representation of cross-cutting state such as cross-references to figures, index entries, and named theorems
 * Additions to the structure of the document - for instance, the blog genre supports the inclusion of raw HTML, and the manual genre supports grouping multiple top-level blocks into a single logical paragraph
 * Procedures for resolving cross references and rendering the document to one or more output formats

All genres use the same {ref "verso-markup"}[markup syntax], and they can share extensions to the markup language that don't rely on incompatible document structure additions.
Mixing incompatible features results in an ordinary Lean type error.
:::

{include 0 UsersGuide.Markup}

{include 0 UsersGuide.Elab}

{include 0 UsersGuide.Extensions}

{include 0 UsersGuide.Output}

{include 0 UsersGuide.Websites}

{include 0 UsersGuide.Manuals}

# Index
%%%
tag := "index"
number := false
%%%

{theIndex}

{include 0 UsersGuide.Releases}

# Dependencies
%%%
tag := "dependencies"
number := false
%%%

This document contains the following open-source libraries, or code derived from them:

{licenseInfo}
