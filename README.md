# Verso: An Authoring Tool for Lean

Writing about Lean takes many forms, including but not limited to:

 * Instructional books such as [Theorem Proving in Lean](https://lean-lang.org/theorem_proving_in_lean4/), [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/), and [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/index.html)
 * Software documentation, such as the Lean users' manual
 * In-source API documentation that is both displayed in IDEs and included in larger documents
 * Descriptions of formalization efforts that connect the formal artifact to mathematical text and guide the formalization, such as those made with Blueprint
 * Web sites and blog posts
 * Research papers in mathematics and computer science that use Lean formalizations in some essential way

Each of these genres needs different tool support than the others, and
many different ways of writing about Lean have come into existence,
including LeanInk, customizations to mdbook and Sphinx, bespoke Python
document management scripts, and doc-gen. But many of these tools share
overlapping concerns: most want to include accurately highlighted
Lean source code, include links to official descriptions of Lean
features, and have internal hyperlinking.

Verso is a collection of libraries for representing documents in Lean
paired with an alternative concrete syntax that allows them to be
written in something very much like Markdown. Documents written in
Verso can make full use of the Lean metaprogramming API to create
arbitrary new features, and these features can be made portable
between genres. The goals of the project are:

 * Be a pleasant tool with which it is enjoyable to write
 * Solid IDE support
 * Support all of the above genres, with the ability for users to add their own genres
 * Empower users to conveniently add their own features to the documentation language
 * Enable but not require extensions to be usable in multiple genres

Verso's design is primarily inspired by
[Scribble](https://docs.racket-lang.org/scribble/index.html) and
[Sphinx](https://www.sphinx-doc.org/en/master/).

## Getting Started

### Examples

The [`verso-templates`](https://github.com/leanprover/verso-templates)
repository contains templates that can serve as a starting point for
Verso-based projects.

### Documentation

The in-progress Verso manual
([HTML](https://github.com/leanprover/verso/releases/download/latest/html-manual.zip),
[PDF](https://github.com/leanprover/verso/releases/download/latest/manual.pdf))
describes the Verso markup language and partially documents the
built-in genres. Today, Verso is usable for running a website and blog
and for writing long-form technical documentation, such as the [Lean
language reference](https://lean-lang.org/doc/reference/latest/).


## Branches and Tags

The workflow described in this section helps Verso development work
well with the automation surrounding Lean releases. Please follow it!
In the past, the `main` branch tracked upstream Lean closely, but
these procedures make it easier to coordinate PRs across many
repositories.

When a Lean release is created, a correponding tag for the compatible
version of Verso is also created. For example, the `v4.19.0` tag
should be used for projects that are built in Lean 4.19.0.

The two most important branches are `main` and `nightly-testing`. The
`main` branch of this repository is intended to work with releases or
release candidates of Lean, while `nightly-testing` tracks Lean
nightlies. When a Lean release candidate is created, `nightly-testing`
is made to work with it, and then its commits are rebased onto `main`.
When the corresponding release is created, the toolchain file on
`main` is updated and the tag is created. To the extent possible,
development occurs on `main`; it is regularly merged into
`nightly-testing`.

When a Lean release occurs, the adaptation changes are squash-merged
into `main` before the tag is created.

## Contributions

The project is currently undergoing change at a rapid pace. If you'd
like to contribute, please get in touch with David Thrane Christiansen
and discuss your plans ahead of time, as there is not presently much
extra time to onboard and supervise new contributors. This may change
as the project matures.

However, one goal of the project is that users should be able to
implement their own extensions without needing to modify the Verso
libraries. If you've attempted to implement your desired feature as an
extension and run into a limitation, please open an issue so we can
try to make the system more extensible.

## Building Documentation

To generate the Verso documentation for Verso itself, run `generate.sh`.

### Customization of Manual Genre HTML

The title of the book being written in the manual genre can be displayed
either at the top of the screen or in the table of contents, depending on
screen width. Books with long titles may wish to add a threshold at which
the title moves to the table of contents using the following CSS:

```css
/* Move the title from the header to the toc when there is not enough room. */
@media screen and (max-width: 1200px) {
  .toc-title {
    display: block;
  }

  .header-title {
    display: none;
  }
}
```

Vary the value `1200px` until there's space for the title. This CSS should be
saved in a served static file and added to the `extraCss` field in the `config`
parameter to `manualMain`.

## Highlighted Lean Code in Verso

Because Lean's parser is extensible, regular-expression-based syntax
highlighting is incapable of accurately identifying keywords or other
tokens. Verso includes libraries that can be used to include accurately
highlighted Lean code in documents, with support for generating HTML
with rich annotations. In particular, tactic proofs are annotated with
their proof states, so the proof can be understood without having to
open the file in a full Lean environment.

The user interface used to implement the display of proof states is
inspired by the excellent [Alectryon](https://github.com/cpitclaudel/alectryon)
by [Clément Pit-Claudel](https://pit-claudel.fr/clement/).

## Cross-Document Cross-References

**Experimental**

In genres that support it, Verso allows linking to other Verso
documents based on _semantic_ information about what is being linked
to, rather than specific URLs. For example, it's possible to link to
"the documentation for `Monad`" rather than
`https://example.com/docs/lib/#Monad`.  To support this, Verso emits a
cross-referencing database that describes the available link targets.

Documented information is organized into _domains_, which are
essentially namespaces. Documents may define whatever domains they
like, and some are provided with Verso. For instance, domains might be
"compiler options" or "constant names" or "syntax categories", but
they might also be "chapters and sections", "technical terminology",
or topics specific to a given document such as "biographies of
historical mathematicians".

Domains contain _objects_, which are identified by a _canonical
name_. For constants, the canonical name is their fully-qualified name
in the environment, while for technical terminology, it's a normalized
form of the term with plural markers removed. Objects may additionally
have arbitrary metadata associated with them, such as the titles of
sections or their position in a table of contents.

Some Verso genres that produce HTML emit a file `xref.json` in the
root of the site. These are the genres that support incoming
cross-references. In a verso project, a site that should be linked to
is referred to as a _remote_, by analogy to Git remotes.

To link to other Verso documents, do the following:
 1. Create a configuration file that describes the remotes to be used
    (see later in this section for an example). It should be called
    `verso-sources.json` and be in the same directory as the
    `lean-toolchain` file.
 2. Run `lake exe verso sync` to download a local mirror of the
    remote's cross-reference information.
 3. Use the configured name for the remote in the `ref` role to link
    to it, e.g. `{ref "canonicalName" (remote := "lean-reference")}[link text]`

Each remote has an update frequency. When building a document, if the
remote is configured to be updated automatically and hasn't been
updated in the specified duration, its cross-references are
fetched. `verso sync` always updates remotes.

When the structure of a remote document changes, but the documented
objects are still present, then rebuilding the current document is
sufficient to fix all broken links. If two documents depend on each
other, then this process may need to be run on both. If documented
objects are removed, then it is an error.

Downloaded remote information is stored in `.verso` in the project
root. The file `verso-xref.json` contains the local copy of each
remote's cross-reference database, while `verso-xref-manifest.json`
tracks when each was updated.

Configuration files are presently JSON, but the plan is to move them
to TOML. While JSON does not support comments, this example file
includes them for explanation:

```json
{ "version": 0, // Version specifier for the configuration file format
  // Configured remotes. Keys are their internal names, used by the author.
  "sources": {
    "manual": {
      // The root of the source. xref.json should be here, and all
      // links will be relative to this:
      "root": "https://lean-lang.org/doc/reference/latest/",
      // How often should it be updated?
      // * "manual" means only when running verso sync,
      // * {"days": N} means every N days
      "updateFrequency": "manual",
      // Ultra-short name shown to readers to disambiguate link texts
      // (e.g. when linking to multiple versions of the same document)
      "shortName": "latest",
      // Longer name shown to readers to explain links
      "longName": "Lean Language Reference"
    }
  }
}
```


## Examples of Verso

The [`examples`](./examples) directory contains example documents
built with the default Verso genres.

### Custom Genre

A minimal example of a Verso genre that includes nontrivial
cross-references can be found in
[`examples/custom-genre`](./examples/custom-genre). To build and run
it, with the output being placed in `./index.html`, use:

```
lake exe simplepage
```

### Website

To build the example website and place the results in
`_out/examples/demosite`, run:
```
lake build
lake exe demosite --output _out/examples/demosite
```

To view the output, a local server will be needed. One way to get such
a server is to use the Python script included in this repository:
```
python3 ./server.py 8880 --directory _out/examples/demosite &
```
after which `http://localhost:8880/` will show the generated site.



### Textbook

The textbook example is both an example that can serve as a template for a
textbook project in Verso and a place where features can be developed
for upstreaming into the manual genre proper.

To build the example website and place the results in
`_out/examples/demotextbook`, run:
```
lake build
lake exe demotextbook --output _out/examples/demotextbook
```

To view the output, a local server will be needed. One way to get such
a server is to use the one from the Python standard library, e.g.
```
python3 -m http.server 8880 --directory _out/examples/demotextbook/html-multi &
```
after which `http://localhost:8880/` will show the generated site.

## Rendering Lean Code

Verso includes an experimental Lean-to-HTML renderer that will convert
Lean code to HTML. This HTML includes hovers, clickable "go to
definition" links, a search function, and rendered intermediate proof
states.

To use this in your project:

1. Add Verso as a package dependency.

   If you're using a `lakefile.toml` configuration, that looks like this:

   ```toml
   [[require]]
   name = "verso"
   git = "https://github.com/leanprover/verso.git"
   rev = "latest"
   ```

   If you're using a `lakefile.lean` configuration, that looks like this:

   ```lean4
   require verso from git "https://github.com/leanprover/verso.git"@"latest"
   ```

   In either case, you probably want to replace `"latest"` with the version of
   Lean you're using: if your `lean-toolchain` file contains 
   `leanprover/lean4:v4.25.0`, then you should replace `"latest"` with 
   `"v4.25.0"`.

2. Generate literate program data from your Lean libraries or modules
   by building their `literate` facet. For library `MyLib`, run:

   ```
   lake build MyLib:literate
   ```

   This generates files in the folder `.lake/build/literate`

3. Generate HTML from this literate program data. To put the HTML in a
   directory named `html`, run:
   
   ```
   lake exe verso-html .lake/build/literate html
   ``` 

You can preview the resulting files by running
`python3 -m http.server 8000 -d html` and pointing a web browser to
http://localhost:8000/

In this output, Verso docstrings and moduledocs are rendered. Setting
`doc.verso` to `true` enables these in source files.

## Licenses

Verso is licensed under the Apache license - please see the file
[LICENSE](./LICENSE) for details.

Verso additionally includes third-party software made available under the MIT
license. These components, and their copyright and licensing information, are
in the [vendored-js](./vendored-js/) directory.
