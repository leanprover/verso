/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoTests.DocStructure.Genre
import VersoTests.DocStructure.Included

open Verso.Tests.DocStructure

/-!
Included documents, with and without an explicit header level.
-/

#doc (StructuralTesting) "Includes" =>

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
