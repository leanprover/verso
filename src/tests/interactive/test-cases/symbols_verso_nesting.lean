import VersoTests.DocStructure.Genre
import VersoTests.DocStructure.Included

open Verso.Tests.DocStructure

-- Document symbols and folding ranges for deep nesting, headers that return to shallower levels,
-- included documents and metadata. Synchronize first so that the whole document is elaborated.
-- The `--^` requests come before the document. After it, they would be paragraph text in its last
-- part, and they would change what the test measures.
--^ sync
--^ textDocument/documentSymbol
--^ textDocument/foldingRange

#doc (StructuralTesting) "Nesting Symbols" =>
%%%
tag := "root"
%%%

Text before any header.

# One
%%%
tag := "one"
%%%

Text in one.

## One A

### One A i

#### One A i x

Text in one A i x.

{include 3 VersoTests.DocStructure.Included}

## One B

{include 2 VersoTests.DocStructure.Included}

# Two
%%%
number := 2
%%%

{include VersoTests.DocStructure.Included}

# Three

## Three A

### Three A i

Text in three A i.

# Four

Text at the end of the document.
