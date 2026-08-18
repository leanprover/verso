/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry
import VersoBlog

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 34, 0⟩
  breaking := true
  tag := "rendered-html-content"
  prs := [964]

open Verso.Output.Html.Files

open Verso.Genre

#doc (Manual) "Rendered HTML Content" =>

A Verso document can now render to a directory of HTML fragments, and the website genre supports integrating these fragments into a particular theme.

:::paragraph
Exported content can be rendered to a directory of fragments, and Verso websites can mount this exported content into their own URL structure, integrating it into their navigation structure and theme.
This feature is described in a {ref "rendered-html"}[dedicated section].
To make it possible for HTML fragments to be reliably bundled with required CSS and JavaScript, several changes were made that affect all rendered HTML:

* Hover text is fetched from the path named by the nearest enclosing element carrying `data-verso-docs`, rather than from a fixed path, so one document holds as many sources of hover text as it holds regions of Verso content.
  The prior behavior is a fallback when no `data-verso-docs` element is found.
* Verso's scripts confine their queries, their listeners, and the data they fetch to the elements they were given, and register their listeners additively, so a page may include scripts from several Verso releases without them interfering with each others' markup.
  The math script marks what it has rendered, preventing double rendering.
* In the blog genre, KaTeX and `marked` are served from the site itself rather than from a CDN, so a page depends on nothing on the network.
* The stylesheets and scripts that traversal accumulates are emitted as file references rather than as inline text, and the assets that have no name of their own are named by a hash of their contents.
* A site's own scripts now skip any subtree marked with `verso-content`, which is what a mounted directory's markup carries, so they reach the site's own pages and nothing that a mount contributed.
:::

# Breaking Changes
%%%
tag := none
%%%
* The types that describe a genre's stylesheets and scripts were moved from the `Verso.Genre.Manual.Files` namespace to `Verso.Output.Html.Files`, where every genre that emits HTML can reach them.
  In particular, {name}`CSS`, {name}`JS`, {name}`StaticCssFile`, {name}`CssFile`, {name}`StaticJsFile`, {name}`JsSourceMap`, and {name}`JsFile` were moved, and the modules `VersoManual.Html.Basic`, `VersoManual.Html.CssFile`, and `VersoManual.Html.JsFile` were replaced by `Verso.Output.Html.Files`.
  The files should be sorted using the helper {name}`Verso.Output.Html.Files.sortByAfter`, which ensures that the ordering constraints between scripts are respected.

* {name}`Blog.Theme.cssFiles` and {name}`Blog.Theme.jsFiles` contain {name}`CssFile` and {name}`JsFile` rather than tuples, as do {name}`Blog.TraverseState.cssFiles` and {name}`Blog.TraverseState.jsFiles`.

* The `path` parameter that the website genre passes to the `post` and `archiveEntry` templates now includes a trailing slash.
  `Blog.dirPathToString` has been replaced by `Verso.Multi.Path.relativeLink`.
  Links to posts and to categories from these templates end in `/`, as the links from the post list already did.

* A theme invokes {name}`Blog.Template.builtinHeader` before defining its own custom properties, so that its definitions override the ones that the header emits.
  {name}`Blog.Theme.default` has been changed accordingly.
  `Verso.Genre.Blog.Traverse.renderMathJs` and `Verso.Output.Html.math.js` have been consolidated to {name}`Verso.Output.Html.mathJs`.
  {name Verso.Output.Html.mathJs}`mathJs` and {name}`Verso.Code.highlightingJs` take the selector for the elements their script belongs to, which is {lean}`"body"` for a whole page.
