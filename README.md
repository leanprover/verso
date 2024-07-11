# Verso: An Authoring Tool for Lean

Writing about Lean takes many forms, including but not limited to:

 * Instructional books such as ...
 * Software documentation, such as the Lean users' manual
 * In-source API documentation that is both displayed in IDEs and included in larger documents
 * Descriptions of formalization efforts that connect the formal artifact to mathematical text and guide the formalization, such as those made with Blueprint
 * Web sites and blog posts
 * Research papers in mathematics and computer science that use Lean formalizations in some essential way

Each of these genres needs different tool support than the others, and
many different ways of writing about Lean have come into existence,
including LeanInk, customizations to mdbook and Sphinx, bespoke Python
document management scripts, doc-gen. But many of these tools share
overlapping concerns - most want to include accurately highlighted
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

Please consult the in-progress Verso manual
([HTML](https://github.com/leanprover/verso/releases/download/latest/html-single-page.zip),
[PDF](https://github.com/leanprover/verso/releases/download/latest/manual.pdf))
for further details. Today, Verso is usable for running a website and
blog, while the other genres are still under development.

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

## Examples

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
a server is to use the one from the Python standard library, e.g.
```
python3 -m http.server 8800 --directory _out/examples/demosite &
```
after which `http://localhost:8800/` will show the generated site.

### Textbook

The textbook example is both an example that can serve as a template for a
textbook project in Verso and a place where features can be developed
for upstreaming into the manual genre proper.

To build the example website and place the results in
`_out/examples/demosite`, run:
```
lake build
lake exe demotextbook --output _out/examples/demotextbook
```

To view the output, a local server will be needed. One way to get such
a server is to use the one from the Python standard library, e.g.
```
python3 -m http.server 8880 --directory _out/examples/demotextbook/html-single &
```
after which `http://localhost:8880/` will show the generated site.

## Licenses

Verso is licensed under the Apache license - please see the file [LICENSE](./LICENSE) for details.

Verso additionally includes third-party software made available under the MIT
license. These components, and their copyright and licensing information, are
in the [vendored-js](./vendored-js/) directory.