/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 34, 0⟩
  breaking := true
  tag := "rendered-html-content"
  prs := []

#doc (Manual) "Rendered HTML Content" =>

A site can now emit its pages as a directory of rendered HTML content, and another site can mount that directory and render it with its own theme.

A directory of rendered HTML content holds page bodies, head requirements, and assets, with no page chrome.
Documentation that is authored in one repository, deployed from another, and kept online for every released version can therefore be themed from one place: a rebuilt site picks up the current navigation bar and colors for content that was built long ago and is never rebuilt.

`Site.toRenderedHtml` and `Site.writeRenderedHtml` produce a directory, `tutorialsRenderedHtmlMain` produces one from a set of tutorials, and the `mount` form of the site configuration language mounts one.
`Site.resolveMounts` reads the manifest of every mount, and `Site.insertMount` inserts a mount from an assembly function that runs in `IO`.

Several changes reach every site rather than only mounted content:

* Hover text is fetched from the path named by the nearest enclosing element carrying `data-verso-docs`, rather than from a fixed path, so one document holds as many sources of hover text as it holds regions of Verso content.
* Verso's scripts confine their queries, their listeners, and the data they fetch to the elements they were given, and register their listeners additively, so a page carries the scripts of several Verso releases without any of them reaching each other's markup. The math script marks what it has rendered.
* KaTeX and `marked` are served from the site itself rather than from a CDN, so a page depends on nothing on the network. This adds roughly a megabyte of KaTeX fonts to every website.
* The stylesheets and scripts that traversal accumulates are emitted as file references rather than as inline text, and the assets that have no name of their own are named by a hash of their contents.
* A site's own scripts skip any subtree marked with `verso-content`, which is what a mounted directory's markup carries, so they reach the site's own pages and nothing that a mount contributed.

Breaking change: the types that describe a genre's stylesheets and scripts now live in `Verso.Output.Html`, where every genre that emits HTML can reach them.
`CSS`, `JS`, `StaticCssFile`, `CssFile`, `StaticJsFile`, `JsSourceMap`, and `JsFile` moved there from `Verso.Genre.Manual`, and the modules `VersoManual.Html.Basic`, `VersoManual.Html.CssFile`, and `VersoManual.Html.JsFile` were replaced by `Verso.Output.Html.Files`.
Code that named these through the manual genre opens `Verso.Output.Html` instead.
The website genre orders its scripts with `Verso.Output.Html.sortByAfter`, so it honors the `after` field that until now only the manual genre respected, and it places `highlighting.js` after `popper.js` and `tippy.js`.
That sort now takes the leftmost script whose named files are already placed, so a script that names nothing keeps the position it had.

Breaking change: `Blog.Theme.cssFiles` and `Blog.Theme.jsFiles` hold `CssFile` and `JsFile` rather than tuples, as do `Blog.TraverseState.cssFiles` and `Blog.TraverseState.jsFiles`.
A theme that wrote `cssFiles := #[("x.css", contents)]` writes `cssFiles := #[{filename := "x.css", contents}]`, and a script can now carry `after` and `defer`.

Breaking change: the `path` parameter that the website genre passes to the `post` and `archiveEntry` templates is a link, ending in `/`, so a template appends a name to it directly.
`Blog.dirPathToString` has been replaced by `Verso.Multi.Path.relativeLink`.
Links to posts and to categories from these templates end in `/`, as the links from the post list already did.

Breaking change: a theme invokes `Blog.Template.builtinHeader` before defining its own custom properties, so that its definitions override the ones that the header emits.
`Blog.Theme.default` has been changed accordingly.
`Verso.Genre.Blog.Traverse.renderMathJs` has been replaced by `Verso.Output.Html.mathJs`, and `Verso.Output.Html.math.js` by the same function.
`mathJs` and `Verso.Code.highlightingJs` take the selector for the elements their script belongs to, which is `"body"` for a whole page.
