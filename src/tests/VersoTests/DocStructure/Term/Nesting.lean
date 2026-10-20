/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoTests.DocStructure.Genre

open Verso.Doc Verso.Tests.DocStructure

/-!
The document of `VersoTests.DocStructure.Nesting`, elaborated all at once by the `#doc` term.
-/

def Verso.Tests.DocStructure.Term.nesting : VersoDoc StructuralTesting := #doc (StructuralTesting) "Nesting" =>

Text before any header.

A second paragraph before any header.

# One

Text in one.

## One A

Text in one A.

### One A i

Text in one A i.

#### One A i x

Text in one A i x.

## One B

Text in one B.

### One B i

# Two

## Two A

### Two A i

Text in two A i.

# Three

Text in three.

* a list
* in three

## Three A

## Three B

## Three C

Text in three C.
