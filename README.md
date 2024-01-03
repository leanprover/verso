# An Authoring Tool for Lean

Writing about Lean takes many forms, including but not limited to:

 * Instructional books such as ...
 * Software documentation, such as the Lean users' manual
 * In-source API documentation that is both displayed in IDEs and included in larger documents
 * Descriptions of formalization efforts that connect the formal artifact to mathematical text and guide the formalization, such as those made with Blueprint
 * Web sites and blog posts
 * Research papers in mathematics and computer science that use Lean formalizations in some essential way

Each of these genres needs different tool support than the others, and many different ways of writing about Lean have come into existence, including LeanInk, customizations to mdbook and Sphinx, bespoke Python document management scripts, doc-gen. But many these tools share overlapping concerns - most want to include accurately highlighted Lean source code, include links to official descriptions of Lean features, and have internal hyperlinking.

LeanDoc is a collection of libraries for representing documents in Lean paired with an alternative concrete syntax that allows them to be written in something very much like Markdown. Documents written in LeanDoc can make full use of the Lean metaprogramming API to create arbitrary new features, and these features can be made portable between genres. The goals of the project are:

 * Be a pleasant tool with which it is enjoyable to write
 * Solid IDE support
 * Support all of the above genres, with the ability for users to add their own genres
 * Empower users to conveniently add their own features to the documentation language
 * Enable but not require extensions to be usable in multiple genres

Please consult the in-progress [LeanDoc manual](https://github.com/leanprover/leandoc/releases/download/latest/manual.pdf) for further details. Today, LeanDoc is usable for running a website and blog, while the other genres are still under development.

## Contributions

The project is currently undergoing change at a rapid pace. If you'd like to contribute, please get in touch with David Thrane Christiansen and discuss your plans ahead of time, as there is not presently much extra time to onboard and supervise new contributors. This may change as the project matures.

However, one goal of the project is that users should be able to implement their own extensions without needing to modify the LeanDoc libraries. If you've attempted to implement your desired feature as an extension and run into a limitation, please open an issue so we can try to make the system more extensible.
