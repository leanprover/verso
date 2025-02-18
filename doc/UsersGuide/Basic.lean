import VersoManual
import UsersGuide.Markup

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Writing Documentation in Lean with Verso" =>

%%%
authors := ["David Thrane Christiansen"]
%%%


Documentation can take many forms:


 * References
 * Tutorials
 * Etc

{include 0 UsersGuide.Markup}

# Genres
%%%
tag := "genres"
%%%


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

## More Docstring Examples

Here are some docstrings as rendered by Verso.
They include heuristic elaboration of code items in their Markdown that attempts to guess what was meant.

{docstring Lean.Syntax}

{docstring List}

{docstring String}

{docstring Subtype}

{docstring OfNat}

{docstring Monad}



:::tactic "induction"
:::

:::tactic "simp"
:::


{docstring Nat}

{optionDocs pp.deepTerms.threshold}

{docstring Thunk}

# Technical Terminology

The `deftech` role can be used to annotate the definition of a {tech}[technical term].
Elsewhere in the document, `tech` can be used to annotate a use site of a technical term.
A {deftech}_technical term_ is a term with a specific meaning that's used precisely, like this one.
References to technical terms are valid both before and after their definition sites.

{docstring deftech}

{docstring tech}

# Index
%%%
number := false
%%%

{theIndex}


# Dependencies
%%%
number := false
%%%

This document contains the following open-source libraries, or code derived from them:

{licenseInfo}
