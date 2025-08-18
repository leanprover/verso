/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Syntax
import VersoManual

open Verso Genre Manual

open Verso.Genre.Manual.InlineLean

#doc (Manual) "Building Documents" =>
%%%
tag := "build-process"
%%%


Verso is a general framework for implementing documentation tools, and this flexibility means that the details of the process described in this section may differ for specific tools.

A Verso document passes through the following steps on its way from its author to its readers:
1. The author writes the document's text in {ref "verso-markup"}[Verso's markup language], which is parsed to Lean's own {name Lean.Syntax}`Syntax` type
2. The document is elaborated to a representation as a Lean data structure
3. The resulting Lean code is compiled to an executable
4. When run, the executable resolves cross-references and computes other globally-scoped metadata in a step referred to as the traversal pass
5. Next, the executable generates the output


# Elaboration
%%%
tag := "elaboration"
%%%

During the elaboration process, Verso's markup language is converted into its internal representation as a Lean inductive type.
When Verso's elaborator encounters an {ref "elab-extensions"}[extension point], it consults an internal table to select an implementation of the extension, and delegates to it.
Other syntax is translated into the appropriate constructors of Verso's data.

All Verso documents are parameterized by their {tech}[genre]:

{docstring Verso.Doc.Genre}

Each document consists of a {name Verso.Doc.Part}`Part`.
The part's title is the title of the entire document.

{docstring Verso.Doc.Part}

{name Verso.Doc.Part}`Part`s contain {name Verso.Doc.Block}`Block`s:

{docstring Verso.Doc.Block}

{name Verso.Doc.Block}`Block`s contain {name Verso.Doc.Inline}`Inline`s:

{docstring Verso.Doc.Inline}

The {name Verso.Doc.Part.metadata}`metadata` field of {name Verso.Doc.Part}`Part` typically gets its value from a metadata block written by the author, though it may be assigned more information during traversal.
The {name Verso.Doc.Block.other}`Block.other` and {name Verso.Doc.Inline.other}`Inline.other` constructors typically result from elaborating {ref "elab-extensions"}[extension points].

# Compilation
%%%
tag := "compilation"
%%%

After elaboration, the document is compiled into an executable program.
Each genre provides a `main` function that will carry out the remainder of the steps.
Usually, this `main` function can be applied to the part that represents the whole document; however, genres that don't have a strict linear order (such as the {ref "website"}[website genre]) will provide their own means of configuring the document's layout.
The `main` function typically also takes configuration parameters both in the code and on the command line, such as which output formats to generate or customizations to the generated output.

# Traversal
%%%
tag := "traversal"
%%%

Because they are Lean values, Verso documents adhere to the structure of Lean programs in general.
In particular, Lean doesn't support cyclic import graphs.
It's common, however, for technical writing to include cyclic references; two sections that describe different aspects of something will frequently refer to one another.
Similarly, a bibliography that's generated from a database needs a global view of a document to include only those works which are, in fact, cited.

The {deftech}_traversal_ phase occurs at runtime, before generating output.
During the traversal phase, the document is repeatedly traversed from beginning to end, and metadata is accumulated into a table.
The document may also be modified during traversal; this allows the title of a section to be inserted into a cross-reference.
This traversal is repeated until the resulting document and metadata tables are not modified; it fails if a set number of passes are executed that result in modifications each time.

Verso provides a general-purpose traversal mechanism for {name Verso.Doc.Part}`Part`, {name Verso.Doc.Block}`Block`, and {name Verso.Doc.Inline}`Inline` that genres may use.
{name Verso.Doc.Genre.TraverseState}`Genre.TraverseState` contains the genre-specific information that's accumulated during traversal, while {name Verso.Doc.Genre.TraverseContext}`Genre.TraverseContext` provides a means of tracking the surrounding document context.
To use this framework, genres should define instances of {name Verso.Doc.Traverse}`Traverse`, which specifies the traversal of a genre's custom elements.
Additionally, instances of {name Verso.Doc.TraversePart}`GenrePart` and {name Verso.Doc.TraverseBlock}`GenreBlock` specify how traversal keeps track of the current position in a document.

{docstring Verso.Doc.Traverse}

{docstring Verso.Doc.TraversePart}

{docstring Verso.Doc.TraverseBlock}

# Output Generation
%%%
tag := "output-gen"
%%%

Following traversal, the readable version of the document is generated.
This may be in any format; each {tech}[genre] defines its supported formats.

Additionally, genres that emit HTML may generate a serialized version of their cross-reference database.
This can be used to automatically maintain the links that implement cross-references between Verso documents: if content moves, rebuilding the linking document is sufficient to fix the link.
