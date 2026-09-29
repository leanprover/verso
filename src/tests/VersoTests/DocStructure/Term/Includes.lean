/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoTests.DocStructure.Genre
import VersoTests.DocStructure.Included

open Verso.Doc Verso.Tests.DocStructure

/-!
The document of `VersoTests.DocStructure.Includes`, elaborated all at once by the `#doc` term.
-/

def Verso.Tests.DocStructure.Term.includes : VersoDoc StructuralTesting := #doc (StructuralTesting) "Includes" =>

Text before the first include.

{include VersoTests.DocStructure.Included}

# Section

Text in section.

## Nested

Text in nested.

{include 2 VersoTests.DocStructure.Included}

{include 1 VersoTests.DocStructure.Included}

# After

Text after the includes.

## After Nested

{include VersoTests.DocStructure.Included}

{include 3 VersoTests.DocStructure.Included}
