/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.DocString.Syntax
import VersoManual
import VersoBlog
import VersoRenderedHtml
import VersoTutorial

open Verso Genre Manual

open Verso.Genre.Blog (Page Post)

open InlineLean
open Verso.Doc

#doc (Manual) "Rendered HTML Content" =>
%%%
tag := "rendered-html"
htmlSplit := .never
%%%

To make it easier to combine documents written in multiple genres, as well as to host historical content such as prior versions of documentation, Verso provides a format for pre-rendered HTML snippets with their associated CSS and JavaScript that can be incorporated into another document.
In particular, this archived content can be placed into the URL hierarchy and site design {ref "website"}[of a Verso-based website].
Pre-rendered content is saved in a directory with a specific structure.
Within a Verso-based website, it can be {deftech}[mounted] at a specific path in the site.

For each page, pre-rendered content provides a set of named {deftech}[fragments] of HTML.
The site in which the content is displayed should place these fragments in the proper places for its design.

# The Directory
%%%
tag := "rendered-html-directory"
%%%

:::paragraph
Saved rendered content is in a directory with the following contents:

: `verso-rendered-html.json`

  This manifest maps page paths to their titles and HTML fragments, and it lists the stylesheets and scripts that the pages need.

: `fragments/`

  This directory contains the HTML fragments that the manifest references.

: `static/`

  This directory contains files that are referenced from the fragments, to be served as-is.
:::


A consumer copies the static directory to its mount point, so, for example, `static/images/screenshot.png` is served at the
mount point followed by `images/screenshot.png`.
It also renders one page per manifest entry.

The static directory includes Verso's CSS and JavaScript along with bundled versions of third-party dependencies, so pages continue to render correctly as Verso changes.
The scripts are confined to the content's own markup, so a page may carry the scripts of several Verso releases alongside those of the consuming site.

{docstring Verso.RenderedHtmlContent}

{docstring Verso.RenderedHtmlContent.Page}

{docstring Verso.RenderedHtmlContent.Fragment}

{docstring Verso.RenderedHtmlContent.Generator}

{docstring Verso.RenderedHtmlContent.Stylesheet}

{docstring Verso.RenderedHtmlContent.Stylesheet.mountPath}

{docstring Verso.RenderedHtmlContent.StylesheetRole}

{docstring Verso.RenderedHtmlContent.Script}

{docstring Verso.RenderedHtmlContent.Library}

{docstring Verso.RenderedHtmlContent.Script.mountPath}

# Page Paths
%%%
tag := "rendered-html-page-paths"
%%%

Page paths are {deftech}_dense_: every proper prefix of a page path is itself a page path, so a directory
always has an index and the root page is always present.
A page keyed `a/b` is served at `a/b/` under the mount point.

{docstring Verso.RenderedHtml.pathToString}

{docstring Verso.RenderedHtml.pathOfString}

{docstring Verso.RenderedHtml.checkDense}

{docstring Verso.RenderedHtml.checkDestinations}

# Fragments
%%%
tag := "rendered-html-fragments"
%%%

Fragments are separate files, and the consuming template places the ones that it knows by name, so neither the producer nor the consumer parses HTML.
Every fragment belongs in the document body.
A fragment that the template does not reference is not rendered, and a consumer should warn about any fragments that it does not place.

:::paragraph
Every fragment is wrapped in a `<div>` with the following classes:
 * `verso-content`
 * The fragment's name
 * The wrapper identifier that the content's scripts use to target their effects

For example:
```
<div
  class="verso-content
    content
    verso-content-9630723502404708584"
  data-verso-docs="...">
  ...
</div>
```

`verso-content` marks a subtree as Verso content and is stable across Verso releases.
The class names inside a fragment's markup are those that the content's own stylesheets style, and they may change from one release to the next.
A site that styles a fragment's markup itself, such as one that places the local table of contents and styles it against `nav.local-toc`, writes its rules against the markup of the release that produced the content, and content from another release may need adaptor rules that bridge the two.
:::

## Conventions
%%%
tag := "fragment-conventions"
%%%

The fragment named `content` holds the page's body and is always present.
A tutorial page also has `localNav` when it has a local table of contents, a code download, or a live editor link.


# The URL Token
%%%
tag := "rendered-html-token"
%%%

Fragments are stored as text, so URLs in them are written relative to a unique token rather than to a fixed
root.
The consumer can relocate the markup in the URL hierarchy via a string replacement operation, rather than by parsing HTML and other languages.

A fragment's token stands for the root of the mounted content.
A consumer replaces it with a prefix such that the token followed by `/x` resolves to `x` under the mount point in the document that the consumer produces.
The token expands with no trailing slash, and the content writes the separator.
Each fragment specifies its own token in the manifest, and the producer chooses a token that does not occur in that fragment's content.

{docstring Verso.RenderedHtml.defaultRootToken}

{docstring Verso.RenderedHtml.chooseToken}

{docstring Verso.RenderedHtml.hasToken}

{docstring Verso.RenderedHtml.substitute}

# Stylesheets, Scripts, and Theming
%%%
tag := "rendered-html-theming"
%%%

A Verso-based website places a mount's stylesheets and scripts through
{name Verso.Genre.Blog.Template.builtinHeader}`builtinHeader`.
A consumer of another kind places them as described here.

Each stylesheet has an associated role.
Stylesheet roles are:

: `variables`

  Defines default values for `--verso-*` custom properties on `:root`.
  Consumers should emit these prior to Verso's defaults and their own themes, so that those will override the included content.

: `content`

  Styles the markup and reads the properties.
  Consumers should emit these last, so that they take precedence over others.
  A role that a consumer does not recognize is placed as `content`.


When a Verso release renames a `--verso-*` property, archived content that reads the earlier name
continues to render, because it carries its own value for that name.
A site that wants such content to follow its theme defines the earlier name in terms of the current
one in an adaptor stylesheet of its own, which applies to every mount, and the archived directory itself is
untouched.

A script under the static directory touches only nodes inside the wrapper that it belongs to.
Each wrapper carries the identifier that its scripts select on, and each script confines its
queries, its listeners, and the data that it fetches to that subtree.
A page therefore carries the scripts of several Verso releases, and of the consuming site, without
any of them affecting each other's markup.

A directory also ships the libraries that its pages need, such as KaTeX, so a site that places
several directories holds several copies of one library, under file names that need not match.
These are plain scripts that assign globals, so the copy placed last owns the global, and their
stylesheets follow the cascade in the same way.
A stylesheet or script that is a copy of a library says which one in `provides`, which is what a
site reads if it decides to place a single copy rather than all of them.

{docstring Verso.Genre.Blog.Template.MountedAssets}

# The Stability Contract
%%%
tag := "rendered-html-contract"
%%%

To enable the display of archived content without rebuilding it, producers and consumers may rely on the following properties:

* Within a format version, the manifest only gains fields, and the format version is incremented only for a change that cannot be expressed as an additional field.
  A consumer reads every format version up to and including its own, ignores unknown fields, and accepts an unrecognized value of an enumerated
  field.

* Fragments are rooted at a `<div>` and carry no `<html>`, `<head>`, `<base>`, `<body>`, or page navigation features.
  Fragments reach a consumer as text, so a consumer relies on this without checking it.

* A title contains only text nodes and the following tags: `em`, `strong`, `code`, `sub`, `sup`, `span` and `br`.
  Additionally, it contains no URLs.
  This makes it safe to be emitted in a heading, link, or list item without being rewritten.
  The title is the one piece of content that a consumer renders on pages other than the content's own, where the content's stylesheets and scripts are absent.

* A fragment's declared token is the only token in its text, and no further substitutions are expected.
  Files under the static directory are served verbatim and are never substituted, so nothing in them refers to a path outside the static
  directory, CSS `url()` included.

* Verso's content stylesheets read `--verso-*` custom properties and hardcode no colors or fonts, and the content ships its own definitions of those properties on `:root`.
  Third-party stylesheets that ship alongside, KaTeX in particular, may set their own colors and fonts.

* A `--verso-*` property keeps its meaning across Verso releases.

* A page keyed `a/b` is served at `a/b/` under the mount point, and `static/foo` at `foo`.
  Conflicts are with respect to the tree that the mount writes, so they involve nothing outside the directory.

* Pages depend on nothing outside the static directory and nothing on the network.

* The format describes one directory.
  How directories are named, where they are found, and what order a site presents them in are decisions of the consumer.

# Producing a Directory
%%%
tag := "rendered-html-producing"
%%%

{docstring Verso.Genre.Blog.Site.toRenderedHtml}

{docstring Verso.Genre.Blog.Site.writeRenderedHtml}

{docstring Verso.Genre.Blog.RenderedHtmlOptions}

{docstring Verso.Genre.Blog.RenderedHtmlOptions.wrapperClass}

{docstring Verso.Genre.Tutorial.tutorialsRenderedHtmlMain}

A producer that writes files into the static directory itself uses these:

{docstring Verso.RenderedHtml.write}

{docstring Verso.RenderedHtml.writeStaticFile}

{docstring Verso.RenderedHtml.Output}

{docstring Verso.RenderedHtml.OutputPage}

{docstring Verso.RenderedHtml.OutputFragment}

# Mounting a Directory
%%%
tag := "rendered-html-mounting"
%%%

In the {ref "website"}[website genre], a site mounts a directory with the `mount` form of the site configuration language.
For example, this site mounts a content directory under `/page/` and another under `/guides/archive/`:
```lean -show
open Verso.Genre.Blog Site Syntax
opaque MySite.Front : Part Page
opaque MySite.Guides : Part Page
```
```lean
def mountingSite : Site := site MySite.Front /
  mount "page" ← "path/to/content"
  "guides" MySite.Guides /
    mount "archive" ← "path/to/older/content" with {
      showInNav := false
    }
```

A mount may appear wherever a directory may: beneath any page, whether at the top level of the site or nested.

{docstring Verso.Genre.Blog.MountSettings}

{docstring Verso.Genre.Blog.Site.resolveMounts}

{docstring Verso.Genre.Blog.Site.insertDir}

{docstring Verso.Genre.Blog.Site.insertMount}

{docstring Verso.RenderedHtml.load}

{docstring Verso.RenderedHtml.Loaded}

Page IDs are namespaced by the mount, because a site that mounts several versions of the same content holds every internal page path once per version.
An author links to a mounted page with the `page_link` role, writing the segments that are not valid Lean identifier components in guillemets, as in `{page_link tutorials.«getting-started»}`.

{docstring Verso.Genre.Blog.mountPageId}

A mount's fragments are provided to the site's template as ordinary template parameters, prefixed by {lean}`"fragments."`.
A per-path override may be used if a special template is required.
The main content of the page is in the `content` fragment, as the parameter `fragments.content`.
{name Verso.Genre.Blog.Template.builtinHeader}`builtinHeader` places the stylesheets and scripts of a mount in the `<head>`.
All themes should use this; if they do, no further support is required in the `<head>` element.
