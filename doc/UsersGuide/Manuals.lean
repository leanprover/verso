/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lean.DocString.Syntax
public import VersoManual
import VersoBlog

open Verso Genre
open Verso.Genre.Manual hiding docstring tactic conv
open Verso.Genre.Manual.DocGen

open InlineLean
open Verso.Doc

set_option pp.rawOnError true

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

# Paragraphs
%%%
tag := "paragraph-directive"
%%%

The {name}`paragraph` directive indicates that a sequence of blocks form a logical paragraph.
Verso's markup language shares one key limitation with Markdown and HTML: bulleted lists and code blocks cannot be contained within paragraphs.
However, there's no _a priori_ reason to reject this, and many real documents include lists in paragraphs.
When using the {name}`paragraph` directive, HTML output wraps the contents in a suitable element that causes their internal margins to be a bit smaller, and TeX output omits the blank line that would signal a paragraph break to TeX.

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

For projects that need to document an external library without importing it, or that use Lean's new module system, the experimental {ref "docgen-docstrings"}[doc-gen-sourced docstring commands] read documentation extracted by doc-gen4 instead.

## Doc-Gen-Sourced Documentation (Experimental)
%%%
tag := "docgen-docstrings"
%%%

:::paragraph
Ordinarily, the `docstring` command extracts documentation directly from the Lean `Environment`.
This requires that the documented library be imported into the Verso document, which has two drawbacks:

 * Declarations from Verso itself and its dependencies are present in the environment alongside the documented library, making it difficult to distinguish the two.
 * Under Lean's new module system, docstrings from other modules are not available.

The `DocGen.docstring` command is an experimental alternative that reads documentation extracted by doc-gen4 rather than from the environment.
It produces the same output as the standard `docstring` command, so the HTML and TeX rendering pipelines work unchanged.
We hope that this will become the standard way to include docstrings in Verso documents.
:::

### Setup

To use doc-gen-sourced docstrings, two pieces of configuration are needed.

First, create a `doc-sources.toml` file in your project root that lists the library targets to document:

```
libraries = ["MyLib", "MyLib.Extra"]
```

Second, add a `needs` declaration to the library target that contains your documentation, so that Lake builds the documentation data before elaborating your document:

```
lean_lib MyDocs where
  needs := #[`@:docSource]
```

After this setup, run `lake build` once to generate the documentation data.
Subsequent builds update it incrementally.

### Usage

Import `VersoManual.DB` and open the `Verso.Genre.Manual.DocGen` namespace.
Then use `DocGen.docstring` in place of `docstring`:

```
{DocGen.docstring Std.HashMap.insert}
```

The `DocGen.docstring` command accepts the same named parameters as the standard `docstring` command: `allowMissing`, `hideFields`, `hideStructureConstructor`, and `label`.

Tactic and conv tactic documentation are available via directives:

```
:::DocGen.tactic "simp"
:::
```

```
:::DocGen.conv "ring_nf"
:::
```

The `DocGen.tactic` directive accepts the same parameters as the standard `tactic` directive, including `show` and `replace`.

### Editor Experience

Before the first `lake build`, `DocGen.docstring` commands show an error directing you to run `lake build`.
After the documentation data has been generated, the editor is fully responsive.
If you change the documented library, running `lake build` again updates the data.

### Coexistence with Environment-Based Commands

The doc-gen-sourced commands live in the `Verso.Genre.Manual.DocGen` namespace and do not replace the standard commands.
Projects that document declarations available in their own environment can continue to use `docstring` with no changes.
Both sets of commands produce the same block types, so they can coexist within a single document if needed.


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
