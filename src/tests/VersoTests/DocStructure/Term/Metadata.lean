/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoTests.DocStructure.Genre

open Verso.Doc Verso.Tests.DocStructure

/-!
The document of `VersoTests.DocStructure.Metadata`, elaborated all at once by the `#doc` term.
-/

def Verso.Tests.DocStructure.Term.metadata : VersoDoc StructuralTesting := #doc (StructuralTesting) "Metadata" =>
%%%
tag := "root"
number := 1
%%%

Text in the root, with a [link][example] and a footnote.[^note]

[example]: https://example.com

# First
%%%
tag := "first"
%%%

Text in first.

[^note]: The footnote text.

## First Nested
%%%
number := 2
%%%

# Second

Text in second, which has no metadata.

[other]: https://example.org

## Second Nested
%%%
tag := "second nested"
number := 3
%%%

Text in second nested, with [another link][other].
