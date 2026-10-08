/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoTests.DocStructure.Genre

open Verso.Tests.DocStructure

/-!
A document that the other document structure samples include.
-/

#doc (StructuralTesting) "Included Document" =>
%%%
tag := "included"
%%%

Text of the included document.

# Included Section

Text of the included section.
