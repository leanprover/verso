import LeanDoc.Genre.Manual
import UsersGuide.Markup

open LeanDoc.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Writing Documentation in Lean" =>

%%%
authors := ["David Thrane Christiansen"]
%%%

Documentation can take many forms:

 * References
 * Tutorials
 * Etc

{include UsersGuide.Markup}

# Genres

:::paragraph
Documentation comes in many forms, and no one system is suitable for representing all of them.
The needs of software documentation writers are not the same as the needs of textbook authors, researchers writing papers, bloggers, or poets.
Thus, Lean's documentation system supports multiple _genres_, each of which consists of:

 * A global view of a document's structure, whether it be a document with subsections, a collection of interrelated documents such as a web site, or a single file of text
 * A representation of cross-cutting state such as cross-references to figures, index entries, and named theorems
 * Additions to the structure of the document - for instance, the blog genre supports the inclusion of raw HTML, and the manual genre supports grouping multiple top-level blocks into a single logical paragraph
 * Procedures for resolving cross references and rendering the document to one or more output formats

All genres use the same markup syntax, and they can share extensions to the markup language that don't rely on incompatible document structure additions.
Mixing incompatible features results in an ordinary Lean type error.
:::
