/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.DocString.Syntax
import VersoManual
import VersoBlog

open Verso Genre Manual

open InlineLean
open Verso.Doc

#doc (Manual) "Manuals and Books" =>
%%%
tag := "manual"
htmlSplit := .never
%%%

Verso's {name}`Manual` genre can be used to write reference manuals, textbooks, or other book-like documents.
It supports generating both HTML and PDFs via LaTeX, but the PDF support is relatively immature and untested compared to the HTML support.

{docstring Manual}

{docstring Manual.PartMetadata}

{docstring Manual.HtmlSplitMode}

The {name}`Manual` genre's block and inline element types are extensible.
In the document, they consist of instances of {name}`Manual.Block` and {name}`Manual.Inline`, respectively:

{docstring Manual.Block}

{docstring Manual.Inline}

The fields {name}`Block.name` and {name Manual.Inline.name}`Inline.name` are used to look up concrete implementations of traversal and output generation in run-time tables that contain descriptions:

{docstring Manual.BlockDescr}

{docstring Manual.InlineDescr}

Typically, the `inline_extension` and `block_extension` commands are used to simultaneously define an element and its descriptor, registering them for use by {name}`manualMain`.

:::paragraph
The type {name}`HtmlAssets` contains CSS and JavaScript code.
{name}`Manual.TraverseState`, {name}`Manual.BlockDescr`, and {name}`Manual.InlineDescr` all inherit from this structure.
During traversal, HTML assets are collected; they are all included in the final rendered document.

{docstring Manual.HtmlAssets}

Use {name}`HtmlAssets.combine` to combine multiple assets.

{docstring Manual.HtmlAssets.combine}

:::

# Tags and References
%%%
tag := "manual-tags"
%%%

The {name}`Manual` genre maintains a table of link targets for various namespaces, such as documented constants, documented syntax, technical terminology, and sections.
In this table, domain-specific names are mapped to their documentation location.
For items such as document sections that don't have a clear, unambiguous, globally-unique name, Verso requires such a name to be manually specified before it is in the table.
Extensions and parts for which names should be manually specified take a `tag` parameter.

:::paragraph
Specifying a tag has the following benefits:
 * The item is included in the quick-jump box and the index.
 * The tag can be used to construct permalinks that will continue to work even if the document is reorganized, so long as the tag is maintained.
 * The item can be linked to automatically from other documents.

Tags should be specified for all sections that the author considers to have a stable identity.
:::

:::paragraph
To refer to a tag, use the {name}`ref` role.
It takes the following parameters:
 * A mandatory _canonical name_, which is the tag assigned to some content.
  By default, this is expected to be a section tag; specifying alternative domains allows the cross reference to be resolved in some other namespace.
 * An optional named argument `domain`, which determines the namespace in which the canonical name is looked up. If no domain is provided, then `domain` defaults to section tags, but other kinds of content may add their cross-references to other namespaces.
 * An optional named argument `remote`, which causes the name to be looked up in data loaded from some other Verso document.
:::

:::paragraph
A {ref "manual-tags"}[reference to this very section] can be created using its tag `"manual-tags"`:
```
{ref "manual-tags"}[reference to this very section]
```
:::

# Paragraphs
%%%
tag := "paragraph-directive"
%%%

The {name}`paragraph` directive indicates that a sequence of blocks form a logical paragraph.
Verso's markup language shares one key limitation with Markdown and HTML: bulleted lists and code blocks cannot be contained within paragraphs.
However, there's no _a priori_ reason to reject this, and many real documents include lists in paragraphs.
When using the {name}`paragraph` directive, HTML output wraps the contents in a suitable element that causes their internal margins to be a bit smaller, and TeX output omits the blank line that would signal a paragraph break to TeX.

# Tables
%%%
tag := "table-directive"
%%%

The {name}`table` directive is used to implement tables.
Tables are written as bulleted list of bulleted lists; the outer lists are rows, and the inner lists are columns; each row must contain the same number of columns.

The flag `header` determines whether the first row should be considered as table data or as headers for the remaining rows.
The named paramter `align`, which may be {name TableConfig.Alignment.left}`left`, {name TableConfig.Alignment.center}`center`, or {name TableConfig.Alignment.right}`right`, determines the alignment of the table with respect to the surrounding text.

::::paragraph
This table maps $`n` to $`n!`:
```
:::table +header (align := center)
*
  * $`n`
  * $`n!`
*
  * 0
  * 1
*
  * 1
  * 1
*
  * 2
  * 2
*
  * 3
  * 6
*
  * 4
  * 24
:::
```

It is rendered as follows:
:::table +header (align := center)
*
  * $`n`
  * $`n!`
*
  * 0
  * 1
*
  * 1
  * 1
*
  * 2
  * 2
*
  * 3
  * 6
*
  * 4
  * 24
:::
::::

# Docstrings
%%%
tag := "docstrings"
%%%

Docstrings can be included using the `docstring` directive. For instance,

```
{docstring List.forM}
```

results in

{docstring List.forM}

The {name}`docstring` command takes a positional parameter which is the documented name.
It also accepts the following optional named parameters:

: `allowMissing : Bool`

  If `true`, missing docstrings are a warning rather than an error.

: `hideFields : Bool`

  If `true`, fields or methods of structures or classes are not shown.

: `hideStructureConstructor : Bool`

  If `true`, constructors of structures or classes are not shown.

: `label : String`

  A label to show instead of the default.

::::paragraph
The {name}`tactic` directive and the {name}`optionDocs` command can be used to show documentation for tactics and compiler options, respectively.

```
:::tactic "induction"
:::
```

results in

:::tactic "induction"
:::

and

```
{optionDocs pp.deepTerms.threshold}
```

results in

{optionDocs pp.deepTerms.threshold}
::::


# Technical Terminology
%%%
shortTitle := "Glossary"
tag := "tech-terms"
%%%

The `deftech` role can be used to annotate the definition of a {tech}[technical term].
Elsewhere in the document, `tech` can be used to annotate a use site of a technical term.
A {deftech}_technical term_ is a term with a specific meaning that's used precisely, like this one.
References to technical terms are valid both before and after their definition sites.

{docstring deftech}

{docstring tech}


# Open-Source Licenses
%%%
tag := "oss-licenses"
%%%

To facilitate providing appropriate credit to the authors of open-source JavaScript, CSS, and HTML libraries used to render a Verso document, inline and block elements can specify the licenses of components that they include in their rendered output.
This is done using the {name HtmlAssets.licenseInfo}`licenseInfo` field that {name}`BlockDescr` and {name}`InlineDescr` inherit from {name}`HtmlAssets`.
These contain a {name}`LicenseInfo`:

{docstring LicenseInfo}

The {name}`licenseInfo` command displays the licenses for all components that were included in the generated document:

{docstring licenseInfo}

# Diagrams
%%%
tag := "diagrams"
%%%

Diagrams can be defined using the `illuminate` library and added to documents using the {name}`diagram` code block.
*This library is experimental, and its API is subject to change.*

:::paragraph
For example, a diagram with a connected circle and rectangle can be rendered using the following code:
````
```diagram (cssWidth := "50%") (texWidth := "0.5\\textwidth")
open Illuminate Diagram in
let c := circle 50 (name := `c)
let r := rect 80 90 (name := `r)
hsep 10 [c, r]
  |>.connectEdge
    { point := `c, angle := some (pi / 4), pull := 0.5 }
    { point := `r, angle := some (2 * pi / 3), pull := 1 }
```
````

It results in the following output:

```diagram (cssWidth := "50%") (texWidth := "0.5\\textwidth")
open Illuminate Diagram in
let c := circle 50 (name := `c)
let r := rect 80 90 (name := `r)
hsep 10 [c, r]
  |>.connectEdge
    { point := `c, angle := some (pi / 4), pull := 0.5 }
    { point := `r, angle := some (2 * pi / 3), pull := 1 }
```
:::
:::paragraph
The {name}`diagram` code block accepts an `inline` flag that marks it for inline rendering in CSS. It also accepts the following named arguments:

: `cssWidth`

  A width in CSS format that is copied verbatim to the width of the output image in HTML.

: `cssScale`

  A scaling factor that relates the diagram's width to `em` in rendered HTML. Use this to have consistent sizing between multiple diagrams.

: `texWidth`

  The `width` parameter passed verbatim to `\includesvg` in TeX output.


:::

Building PDFs from LaTeX output relies on the `svg` LaTeX package, which calls Inkscape to convert each emitted SVG to PDF at build time.
This requires `inkscape` on the `PATH` as well as running `lualatex` with the `-shell-escape` flag.
This flag allows LaTeX to execute arbitrary commands during compilation.

# Themes
%%%
tag := "manual-themes"
%%%

The manual genre includes support for themes.
Authors may select any number of themes to include, and readers may select any of these themes while reading.
A theme for a manual includes a {ref "output-code-themes"}[code theme], in addition to selecting fonts and colors for the text and navigation interface.

## Overview
%%%
tag := "manual-themes-overview"
%%%

The rendered HTML for a manual includes a "gear" button in the header that opens a popover widget.
This widget offers two choices:
 * A single theme, to be chose from a list and always used
 * A light theme and a dark theme, to be selected automatically based on the browser's `prefers-color-scheme` setting.


## The `ManualTheme` Structure
%%%
tag := "manual-themes-structure"
%%%

Authors specify a manual theme as a definition of type {name Verso.Theme.ManualTheme}`ManualTheme`.
Manual themes must be registered using the `@[manual_theme]` attribute.
Manual themes extend {ref "output-code-themes"}[code themes] with fonts and colors for textual content and navigation features.

{docstring Theme.ManualTheme}

## Built-In Themes
%%%
tag := "manual-themes-builtins"
%%%


```lean -show
open Verso.Theme in
/--
info:
Alucard (Verso.Theme.ManualTheme.alucard)
Argent (Verso.Theme.ManualTheme.argent)
Beacon Dark (Verso.Theme.ManualTheme.beaconDark)
Beacon Light (Verso.Theme.ManualTheme.beaconLight)
Chromatic Dark (Verso.Theme.ManualTheme.chromaticDark)
Chromatic Light (Verso.Theme.ManualTheme.chromaticLight)
Dracula (Verso.Theme.ManualTheme.dracula)
Hearth Dark (Verso.Theme.ManualTheme.hearthDark)
Hearth Light (Verso.Theme.ManualTheme.hearthLight)
Ink (Verso.Theme.ManualTheme.ink)
Nord (Verso.Theme.ManualTheme.nord)
Nord Light (Verso.Theme.ManualTheme.nordLight)
Sandstone Dark (Verso.Theme.ManualTheme.sandstoneDark)
Sandstone Light (Verso.Theme.ManualTheme.sandstoneLight)
Slate (Verso.Theme.ManualTheme.slate)
Solarized Dark (Verso.Theme.ManualTheme.solarizedDark)
Solarized Light (Verso.Theme.ManualTheme.solarizedLight)
Steel (Verso.Theme.ManualTheme.steel)
-/
#guard_msgs in
#eval show IO Unit from do
  let table : ManualThemeTable := manual_themes%
  let entries := table.themes.toList.map
    (fun (p : Lean.Name × ManualTheme) => s!"{p.snd.name} ({p.fst})")
  IO.println ""
  for line in entries.toArray.qsort (· < ·) do
    IO.println line
```

### Defaults: Ink and Argent
%%%
tag := "manual-default-themes"
%%%

The default light and dark themes are called _Ink_ and _Argent_, respectively.
These themes use understated formatting, relying on typographical features such as weight and slant syntax and semantic highlighting.

### Other Included Themes
%%%
tag := "manual-other-themes"
%%%

The remaining shipped themes fall into seven families, each with a light variant and a dark variant.

: Chromatic

  The _Chromatic_ themes are versions of _Ink_ and _Argent_ that use color in addition to typographical features for syntax highlighting.

: Beacon

  The _Beacon_ themes are variants of _Ink_ and _Argent_ that use the [Okabe-Ito palette](https://jfly.uni-koeln.de/color/) to ensure that different colors are distinct for readers with various forms of colorblindness.

: Solarized

  These themes use Schoonover's [Solarized](https://ethanschoonover.com/solarized/) palettes.
  Note that these low-contrast themes are not particularly accessible, and thus should probably not be the default theme for a document.

: Dracula and Alucard

  _Dracula_ and _Alucard_ implement the [Dracula](https://draculatheme.com/spec) family of themes.


: Nord

  Greb's arctic, north-bluish [Nord](https://www.nordtheme.com/) palette in a Polar Night dark variant and a Snow Storm light variant.

: Sandstone

  The _Sandstone_ themes are a warm-sepia family: a cream-with-terracotta light variant and a deep canyon-shadow dark variant, both inspired by the deserts of the Southwest USA.

: Steel and Slate

  _Steel_ and _Slate_ use cool, high-contrast neutral colors.

: Hearth

  The _Hearth_ themes have a cream-and-sage light variant and a candlelit deep-olive dark variant, and use serif fonts.



## Configuration
%%%
tag := "manual-themes-configuration"
%%%

The following fields of {name}`RenderConfig` are relevant to themes:

: {name RenderConfig.availableThemes}`availableThemes`

  This field lists the available themes. By default, it contains all themes that are registered with `@[manual_theme]`.
  Authors can restrict readers to a subset of the registered themes by listing the desired themes here.

: {name RenderConfig.defaultLightTheme}`defaultLightTheme`

  When readers have configured their themes to follow the system preference, this is the default light theme.

: {name RenderConfig.defaultDarkTheme}`defaultDarkTheme`

  When readers have configured their themes to follow the system preference, this is the default dark theme.

: {name RenderConfig.defaultSingleAppearance}`defaultSingleAppearance`

  When readers have configured their themes to ignore the browser's request, this is the default theme. It may be light or dark.


## Accessibility Checking
%%%
tag := "manual-themes-accessibility"
%%%

By default, manual themes are checked for common accessibility problems, including insufficient contrast between text and background and the use of colors that not all readers can distinguish.
Verso issues a warning when an inaccessible theme is included, and it is an error when an inaccessible theme is the default.
These checks are incomplete: themes may have accessibility problems that are not related to their choices of colors, and the automated tests do not take custom CSS into account.


: {name Config.strictThemeCoverage}`strictThemeCoverage`

  Verifies that the set of available themes offers at least one accessible choice for each appearance a reader might select.
  With a single available theme, that theme must be accessible; with multiple available themes, at least one accessible light theme and one accessible dark theme must exist.
  If {lean}`true` (the default), failing this check is an error.
  If {lean}`false`, failing this check results in a warning.

: {name Config.strictDefaultThemeAccessibility}`strictDefaultThemeAccessibility`

  When {name}`true` (the default), Verso verifies that the configured {name RenderConfig.defaultLightTheme}`defaultLightTheme` and {name RenderConfig.defaultDarkTheme}`defaultDarkTheme` are accessible.
  It is an error if either fails the accessibility check.

: {name Config.warnPerThemeAccessibility}`warnPerThemeAccessibility`

  Emits a build-log warning for every registered theme that has accessibility issues, naming the theme and the specific colors involved.
  Defaults to {lean}`true`; set it to {lean}`false` to silence the per-theme advisories.

### Downgrading Documented Trade-Offs
%%%
tag := "manual-themes-accessibility-downgrade"
%%%

Not all themes included with Verso are accessible to all readers.
This is intentional on the part of their designers.
For example, the _Solarized_ themes are intentionally low-contrast, and _Beacon Light_ prioritizes the Okabe-Ito palette's distinguishability for many varieties of color perception over contrast.

By default, Verso warns about these themes if they're included in {name RenderConfig.availableThemes}`availableThemes`.
To silence this warning, set {name Config.warnPerThemeAccessibility}`warnPerThemeAccessibility` to {name}`false`.
By default, it is an error if a non-accessible theme is set as the default theme.
Set {name Config.strictDefaultThemeAccessibility}`strictDefaultThemeAccessibility` to {name}`false` to disable this error.


## PDF Output
%%%
tag := "manual-themes-pdf"
%%%


PDF output via TeX uses only a {ref "output-code-themes"}[code theme].
The {name RenderConfig.pdfCodeTheme}`pdfCodeTheme` configuration field selects the code theme to be used to generate PDFs, defaulting to {name Theme.CodeTheme.ink}`ink`.
This setting ignores the theme used for HTML output.
The preamble in the resulting TeX uses `xcolor`'s `\definecolor` to define a named LaTeX color for each themeable color.
Code is generated using _semantic_ macros such as `\versoVar` and `\versoConst`, so a `\renewcommand` is also generated to configure each category.
