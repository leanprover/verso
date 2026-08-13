/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
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

open Verso.Output

open Verso.Code

#doc (Manual) "HTML" =>
%%%
tag := "output-html"
%%%

While most users of Verso don't need to worry about the specific details of the HTML that it produces, authors of new {tech}[genres] or of substantial extensions to existing genres may need to produce custom HTML.
Verso's HTML output follows a number of conventions and uses built-in libraries and features.

Verso's {name}`Html` type represents HTML documents.
They are typically produced using an embedded DSL that is available when the namespace `Verso.Output.Html` is opened.

{docstring Html}

{docstring Html.empty}

{docstring Html.fromArray}

{docstring Html.fromList}

{docstring Html.append}

{docstring Html.visitM}

{docstring Html.format}

{docstring Html.asString}

HTML documents are written in double curly braces, in a syntax very much like HTML itself.
The differences are:
 * Double curly braces escape back to Lean. This can be done for HTML elements, attribute values, or whole sets of attributes.
 * Text content is written as Lean string literals to facilitate precise control over whitespace.
 * Interpolated Lean strings (with `s!`) may be used in any context that expects a string.

For example, this definition creates a `<ul>` list:
```lean -keep (name := htmllist)
open Verso.Output.Html

def mkList (xs : List Html) : Html :=
  {{ <ul> {{ xs.map ({{<li>{{·}}</li>}}) }} </ul>}}

#eval mkList ["A", {{<emph>"B"</emph>}}, "C"]
  |>.asString
  |> IO.println
```

```leanOutput htmllist
<ul>
  <li>
    A</li>
  <li>
    <emph>B</emph></li>
  <li>
    C</li>
  </ul>
```

# Conventions
%%%
tag := "html-conventions"
%%%

:::paragraph
While Verso genres may generate whatever output is necessary, some aspects of the Verso infrastructure make assumptions about generated HTML.
In particular, Verso assumes that HTML follows these conventions:
* Each page contains a `<base>` tag that points at the site root, and all URLs are relative to the site root.
* Pages are served as directories that contain an `index.html` file, rather than as bare HTML files. In other words, instead of `page.html`, the page should be served as `page/index.html`. This affects the meaning of relative URLs.
:::

## CSS
%%%
tag := "html-conventions-css"
%%%
The names of CSS variables that are intended for customization begin with `--verso-`, with a single `-` before the variable's name.
Variables that are a part of the Verso implementation and are not intended to be directly customized use two `-` characters, and thus begin with `--verso--`.

The customizable variables and their default values are defined in `verso-vars.css`, which is included as the string constant {name}`Html.«verso-vars.css»`.
Each page should include this stylesheet.

{docstring Html.«verso-vars.css»}

## Lean Code in HTML
%%%
tag := "html-conventions-lean-code"
%%%

Lean code is rendered using a set of built-in CSS rules.
The colors and fonts that they use are controlled by CSS variables, documented in `verso-vars.css`.

Each category of token that can be highlighted supports customization of its color, font weight, font style, and font family.
Constants (such as `List` or `id`) are controlled by the `--verso-code-const-` family, keywords (such as `def` or `induction`) by the `--verso-code-keyword-` family, and local bindings (such as `x` in `let x := 5`) by the `--verso-code-var-` family.
For example, keywords are styled by `--verso-code-keyword-color`, `--verso-code-keyword-weight`, `--verso-code-keyword-style`, and `--verso-code-keyword-font-family`.

:::paragraph
Each message severity (info, warning, and error) has four sets of related styles, exemplified here for the `error` severity:

* the affected code itself, via `--verso-code-error-color`, `--verso-code-error-bg-color`, `--verso-code-error-hover-color`, and `--verso-code-error-hover-bg-color`, plus `--verso-error-indicator-color` for the wavy underline that marks the presence of a message,
* the text of the message, via `--verso-message-error-color`,
* the tooltip that displays the message, via `--verso-tooltip-error-color`, `--verso-tooltip-error-bg-color`, and `--verso-tooltip-error-border-color`, and
* the marker bar on output blocks, via `--verso-output-error-color`.
:::

Tooltips share a generic palette (`--verso-tooltip-color`, `--verso-tooltip-bg-color`, `--verso-tooltip-border-color`, and `--verso-tooltip-separator-color`) that the severity-specific tooltip colors default to.
Proof states are styled by the `--verso-tactic-state-` and `--verso-tactic-toggle-` variable families, and the hover highlight on interactive code by `--verso-code-hover-bg-color`.

Data intended for hovers is deduplicated while generating HTML.
The content of all hovers is saved in `-verso-docs.json` in the site root.
The `data-verso-hover` attribute stores the index of the hover information in this file.

:::paragraph
Rendering highlighted code requires supporting CSS and JavaScript on each page that contains it:

* {name}`highlightingStyle` contains the CSS rules that style highlighted code.
* {name}`highlightingJs` produces JavaScript code that displays hovers and highlights other occurrences of an identifier. By default, it obtains hover content using {name}`fetchDocsJson`.
* Hovers are displayed using the `tippy.js` and `popper.js` libraries. Copies of them are included as the string constants {name}`Highlighted.WebAssets.tippy` and {name}`Highlighted.WebAssets.popper`, with source maps {name}`Highlighted.WebAssets.tippy.map` and {name}`Highlighted.WebAssets.popper.map` and a stylesheet {name}`Highlighted.WebAssets.tippy.border.css`.
* Markdown in documentation shown in hovers is rendered by the `marked` library, included as the string constant {name}`Highlighted.WebAssets.marked` with source map {name}`Highlighted.WebAssets.marked.map`.
:::

{docstring highlightingStyle}

{docstring highlightingJs}

{docstring fetchDocsJson}

## Math
%%%
tag := "html-conventions-math"
%%%

TeX-style mathematical notation (written `` $`f(x)` `` or `` $$`f(x)` ``, and represented by the {name}`Inline.math` constructor) is rendered to a `<code>` element with the class `math`, together with the class `inline` or `display` according to the requested mode.
The element's text content is the TeX code, which is not processed while generating HTML.
For example, `` $`\frac{1}{2}` `` is represented in HTML as `<code class="math inline">\frac{1}{2}</code>`.

Math is typeset in the browser using the bundled KaTeX library.
When a page has loaded, the script in {name}`Html.math.js` renders every element with these classes.
Pages that contain mathematical notation should include this script together with KaTeX itself: its stylesheet ({name}`Html.katex.css`), its code ({name}`Html.katex.js`), and its fonts ({name}`Html.katexFonts`).
The stylesheet refers to the fonts by relative paths, so the file layout described in their docstrings should be preserved.

{docstring Html.katex.css}

{docstring Html.katex.js}

{docstring Html.katexFonts}

{docstring Html.math.js}
