/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.DocString.Syntax
import VersoManual
import VersoManual.InlineLean
import VersoBlog


open Verso Genre Manual

open Verso.Genre.Blog (Page Post)
open Verso.Genre.Manual.InlineLean

open InlineLean
open Verso.Doc

open Verso.Output

#doc (Manual) "Output Formats" =>
%%%
tag := "outputs"
htmlSplit := .never
%%%

Verso provides genre authors with tools for generating HTML and TeX code via embedded languages that reduce the syntactic overhead of constructing ASTs.
These libraries may also be used by authors of extensions to the {name}`Manual` genre, who need to define how each new element should be rendered to each supported backend.

# HTML
%%%
tag := "output-html"
%%%

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

# TeX
%%%
tag := "output-tex"
%%%


Verso's {name}`TeX` type represents LaTeX documents.
They are typically produced using an embedded DSL that is available when the namespace `Verso.Output.TeX` is opened.

{docstring TeX}

{docstring TeX.empty}

{docstring TeX.asString}

TeX documents are written in `\TeX{...}`, in a syntax very much like LaTeX itself.
The differences are:
 * `\Lean{...}` escapes back to Lean, expecting a value of type {name}`TeX`.
 * Text content is written as Lean string literals to facilitate precise control over whitespace.
 * Interpolated Lean strings (with `s!`) may be used in any context that expects a string.

For example, this definition creates a bulleted list list:
```lean -keep (name := texlist)
open Verso.Output.TeX

def mkList (xs : List TeX) : TeX :=
  \TeX{
    \begin{itemize}
      \Lean{xs.map (\TeX{\item " " \Lean{·} "\n"})}
    \end{itemize}
  }

#eval mkList ["A", \TeX{\emph{"B"}}, "C"]
  |>.asString
  |> IO.println
```

```leanOutput texlist
\begin{itemize}
\item A
\item \emph{B}
\item C

\end{itemize}
```

# Themes for Code
%%%
tag := "output-code-themes"
%%%

A {deftech}_code theme_ is a genre-neutral description of how rendered code should look, including colors, token styling, and font choices.
Any Verso genre can use code themes.
The built-in {name}`Manual` genre extends code themes with further fonts and colors.
Please refer to its {ref "manual-themes"}[theming] documentation for more information.

A code theme is a value of type {name Theme.CodeTheme}`CodeTheme` with the `@[code_theme]` attribute.

## Colors and Palettes
%%%
tag := "code-themes-colors"
%%%

```lean -show
open Verso.Theme
```



### The `Color` Type and `color%` Literal
%%%
tag := "code-themes-color-type"
%%%

Colors are represented by the {name}`Color` type.

{docstring Verso.Theme.Color}

{docstring Verso.Theme.Color.rgb}

A number of built-in color constants are provided:

{docstring Verso.Theme.Color.white}

{docstring Verso.Theme.Color.black}

{docstring Verso.Theme.Color.gray}

{docstring Verso.Theme.Color.red}

{docstring Verso.Theme.Color.green}

{docstring Verso.Theme.Color.blue}

{docstring Verso.Theme.Color.transparent}

### Named Reference Palettes
%%%
tag := "code-theme-palettes"
%%%

To support bundled themes, Verso ships with a number of popular color palettes.
Each palette has an associated namespace that contains the named colors from the palette along with a `name : String` and a `sourceLink` of type {name}`SourceLink`, which is a source that can be linked to in theme-selection UIs.

{docstring Theme.SourceLink}

: Okabe-Ito

  Masataka Okabe and Kei Ito's eight-hue colorblind-safe palette, published in 2002 as part of their guidance on [accessible color use in scientific visualization](https://jfly.uni-koeln.de/color/).
  The hues stay distinguishable under protanopia, deuteranopia, and tritanopia, which makes them a standard reference set for code highlighting that must remain readable to dichromat readers.
  The namespace `Verso.Theme.Color.Palettes.OkabeIto` provides {name Verso.Theme.Color.Palettes.OkabeIto.black}`black`, {name Verso.Theme.Color.Palettes.OkabeIto.orange}`orange`, {name Verso.Theme.Color.Palettes.OkabeIto.skyBlue}`skyBlue`, {name Verso.Theme.Color.Palettes.OkabeIto.bluishGreen}`bluishGreen`, {name Verso.Theme.Color.Palettes.OkabeIto.yellow}`yellow`, {name Verso.Theme.Color.Palettes.OkabeIto.blue}`blue`, {name Verso.Theme.Color.Palettes.OkabeIto.vermillion}`vermillion`, and {name Verso.Theme.Color.Palettes.OkabeIto.reddishPurple}`reddishPurple`.

: Solarized

  Ethan Schoonover's standard cream-on-paper palette of sixteen colors: eight [monotones](https://ethanschoonover.com/solarized/) plus eight accent hues.
  Schoonover's rebasing rule splits the monotones by substrate: `base0` and `base1` are dark-mode foreground tones (body text and emphasized content, respectively), `base00` and `base01` are the light-mode counterparts, and the four remaining shades (`base02`, `base03`, `base2`, `base3`) are background and highlight tones for each substrate.
  The namespace `Verso.Theme.Color.Palettes.Solarized` provides {name Verso.Theme.Color.Palettes.Solarized.base03}`base03` through {name Verso.Theme.Color.Palettes.Solarized.base3}`base3` for the monotones and {name Verso.Theme.Color.Palettes.Solarized.yellow}`yellow`, {name Verso.Theme.Color.Palettes.Solarized.orange}`orange`, {name Verso.Theme.Color.Palettes.Solarized.red}`red`, {name Verso.Theme.Color.Palettes.Solarized.magenta}`magenta`, {name Verso.Theme.Color.Palettes.Solarized.violet}`violet`, {name Verso.Theme.Color.Palettes.Solarized.blue}`blue`, {name Verso.Theme.Color.Palettes.Solarized.cyan}`cyan`, and {name Verso.Theme.Color.Palettes.Solarized.green}`green` for the accent hues.

: Dracula and Alucard

  The canonical dark Dracula palette and its light-substrate counterpart Alucard, from the [official Dracula spec](https://draculatheme.com/spec).
  Each palette shares twelve color slots — background, current line, selection, foreground, comment, red, orange, yellow, green, cyan, purple, pink — with documented semantic intent that ports the palette into syntax highlighting (pink for keywords, cyan for classes and types, orange for numbers and booleans, yellow for strings, green for functions, purple for instance reserved words, red for errors).
  The namespaces `Verso.Theme.Color.Palettes.DraculaClassic` and `Verso.Theme.Color.Palettes.AlucardClassic` each provide the twelve named colors.

: Nord

  Sven Greb's arctic, north-bluish palette of sixteen colors organized in [four groups](https://www.nordtheme.com/docs/colors-and-palettes): *Polar Night* ({name Verso.Theme.Color.Palettes.Nord.nord0}`nord0` through {name Verso.Theme.Color.Palettes.Nord.nord3}`nord3`) for dark-substrate backgrounds and code surfaces, *Snow Storm* ({name Verso.Theme.Color.Palettes.Nord.nord4}`nord4` through {name Verso.Theme.Color.Palettes.Nord.nord6}`nord6`) for body text on dark backgrounds and substrates on light variants, *Frost* ({name Verso.Theme.Color.Palettes.Nord.nord7}`nord7` through {name Verso.Theme.Color.Palettes.Nord.nord10}`nord10`) for the canonical syntax accents, and *Aurora* ({name Verso.Theme.Color.Palettes.Nord.nord11}`nord11` through {name Verso.Theme.Color.Palettes.Nord.nord15}`nord15`) for warm accent hues used by diagnostics and additional syntax categories.
  The namespace `Verso.Theme.Color.Palettes.Nord` provides each numbered constant.

## Fonts and Typefaces
%%%
tag := "code-themes-fonts"
%%%

The {name}`Typeface` type represents a general typeface.
There are three built-in faces, {name}`Typeface.sans`, {name}`Typeface.serif`, and {name}`Typeface.mono`, which stand for unspecified sans-serif, serif, and monospaced font faces.
Specific font faces may be provided using the {name}`Typeface.files` constructor, which bundles font files with sufficient metadata to use them in a theme.

{docstring Typeface}


### `define_font_face`
%%%
tag := "code-themes-fonts-def"
%%%

To make it easier to include custom fonts, Verso provides the `define_font_face` command, which declares a {name}`FontFace` value by name and embeds the font file into the resulting `.olean` at compile time.
This allows themes that include fonts to be distributed as ordinary Lean libraries.

{docstring Verso.defineFontFace}

These {name}`FontFace` declarations are then composed into a {name}`Typeface` via the {name}`Typeface.files` constructor.

## The `CodeTheme` Structure
%%%
tag := "code-themes-structure"
%%%

{docstring Theme.CodeTheme}

Remember to register code themes using the `@[code_theme]` attribute.

## Accessibility Checking
%%%
tag := "code-themes-accessibility"
%%%

Code themes are checked for accessibility.
These checks are by nature incomplete: they can discover the _presence_ of problems, but not their absence.
Nonetheless, ensuring that the default theme used by a document passes these tests is a good first step towards accessbility.

{docstring Theme.CodeTheme.checkAccessibility}

The check compares the color fields of a {name Theme.CodeTheme}`CodeTheme` and returns an array of {name Theme.Color.Issue}`Issue` values, one per problem found.

Themes may contain arbitrary CSS.
In this case, some other means of checking accessibility should be used.

### Contrast
%%%
tag := "code-themes-accessibility-contrast"
%%%
The contrast checker uses two thresholds: WCAG AA's 4.5:1 ratio for primary text and 3:1 for UI accents and large-text positions.

The following contrasts are checked at the text threshold (4.5:1):

 * Body, error-message, warning-message, and info-message text against the page background.
 * Each themed token color against the code-block background.
 * The code color against the inline-code background, when one is set.
 * The code color against both highlight backgrounds, and body text against the prose-highlight background.
 * Hover-popup text against the hover-popup background and against the tactic-state background.
 * Code against the tactic-state background.

The following contrasts are checked at the large text threshold (3:1):

 * Each diagnostic accent (error, warning, info indicator) against the page background.
 * The neutral UI-element color against the code-block background.
 * The tactic-state border against the tactic-state background.

Images that contain text are not automatically checked, and must be checked for accessiblity in some other way.

### Color Perception
%%%
tag := "code-themes-accessibility-perception"
%%%

The eleven token colors are checked for perceptual distinctness in four separate modes:
 * unmodified
 * simulated protanopia
 * simulated deuteranopia
 * simulated tritanopia.

Every pair must remain perceptibly distinct (CIEDE2000 ΔE above a tunable threshold).
A pair of _identical_ colors is not an issue, because such themes have explicitly decided not to distinguish that pair using color.

A translucent foreground is composited over its background (via {name Theme.Color.over}`Color.over`) before checking.
A translucent _background_, by contrast, is itself reported as a contrast issue, because the effective backdrop is unknown.


### The `Issue` Type
%%%
tag := "code-themes-accessibility-issues"
%%%

Issues are reported using the type {name Theme.Color.Issue}`Issue`, which describes the accessibility issue.

{docstring Theme.Color.Issue}
