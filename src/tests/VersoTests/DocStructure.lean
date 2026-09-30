/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import VersoTests.DocStructure.Genre
import VersoTests.DocStructure.Included
import VersoTests.DocStructure.Nesting
import VersoTests.DocStructure.Metadata
import VersoTests.DocStructure.Includes
import VersoTests.DocStructure.Term.Nesting
import VersoTests.DocStructure.Term.Metadata
import VersoTests.DocStructure.Term.Includes

set_option doc.verso true

/-!
Tests of the parts that document elaboration produces.

The sample documents in {lit}`VersoTests.DocStructure` are elaborated three ways: block by block by
the {lit}`#doc` command, and all at once by {lit}`#docs` and by the {lit}`#doc` term. All three
must produce the same parts. The tests compare them with golden files.
-/

open Verso.Doc
open Errata

namespace Verso.Tests.DocStructure.Docs

/- The document of `VersoTests.DocStructure.Nesting`, elaborated all at once by `#docs`. -/
#docs (StructuralTesting) nesting "Nesting" :=
:::::::

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
:::::::

/- The document of `VersoTests.DocStructure.Metadata`, elaborated all at once by `#docs`. -/
#docs (StructuralTesting) metadata "Metadata" :=
:::::::
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
:::::::

/- The document of `VersoTests.DocStructure.Includes`, elaborated all at once by `#docs`. -/
#docs (StructuralTesting) includes "Includes" :=
:::::::

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
:::::::

end Verso.Tests.DocStructure.Docs

namespace Verso.Tests.DocStructure

/-- The directory that holds the golden files and the test output. -/
def baseDir : System.FilePath := "src/tests/integration/doc-structure"

/--
Renders each document's parts to {lit}`output/<dir>/<name>.txt`, then compares the output with the
golden files in {lit}`expected`.
-/
def checkStructure (dir : String) (docs : List (String × Part StructuralTesting)) : Test := do
  let output := baseDir / "output" / dir
  if ← output.pathExists then IO.FS.removeDirAll output
  IO.FS.createDirAll output
  for (name, part) in docs do
    IO.FS.writeFile (output / s!"{name}.txt") (renderPart part)
  goldenDir (baseDir / "expected") output

/-- The documents elaborated block by block by the {lit}`#doc` command match the golden files. -/
@[test]
def docCommand : Test :=
  checkStructure "doc-command" [
    ("nesting", %doc VersoTests.DocStructure.Nesting),
    ("metadata", %doc VersoTests.DocStructure.Metadata),
    ("includes", %doc VersoTests.DocStructure.Includes)
  ]

/-- The documents elaborated all at once by {lit}`#docs` match the golden files. -/
@[test]
def docsCommand : Test :=
  checkStructure "docs-command" [
    ("nesting", Docs.nesting.toPart),
    ("metadata", Docs.metadata.toPart),
    ("includes", Docs.includes.toPart)
  ]

/-- The documents elaborated all at once by the {lit}`#doc` term match the golden files. -/
@[test]
def docTerm : Test :=
  checkStructure "doc-term" [
    ("nesting", Term.nesting.toPart),
    ("metadata", Term.metadata.toPart),
    ("includes", Term.includes.toPart)
  ]

end Verso.Tests.DocStructure

namespace Verso.Tests.DocStructure.Errors

/- Errors for badly structured parts. -/

/--
error: Wrong header nesting - got ### but expected at most ##
-/
#test_msgs in
#docs (StructuralTesting) wrongNesting "Wrong Nesting" :=
:::::::
# One

### Too Deep

Text.
:::::::

/--
error: Wrong header nesting - got ### but expected at most ##
-/
#test_msgs in
#docs (StructuralTesting) wrongNestingAfterClose "Wrong Nesting After Closing Several Parts" :=
:::::::
# A

## B

### C

# D

### E
:::::::

/--
error: Wrong header nesting - got ## but expected at most #
-/
#test_msgs in
#docs (StructuralTesting) wrongNestingAtRoot "Wrong Nesting at the Root" :=
:::::::
## Too Deep
:::::::

/--
error: Metadata blocks must precede both content and subsections
-/
#test_msgs in
#docs (StructuralTesting) metadataAfterContent "Metadata After Content" :=
:::::::
Text.

%%%
tag := "late"
%%%
:::::::

/--
error: Metadata blocks must precede both content and subsections
-/
#test_msgs in
#docs (StructuralTesting) metadataAfterContentInSection "Metadata After Content in a Section" :=
:::::::
# Section

Text.

%%%
tag := "late"
%%%
:::::::

/--
error: Metadata blocks must precede both content and subsections
-/
#test_msgs in
#docs (StructuralTesting) metadataAfterSubPart "Metadata After a Sub-Part" :=
:::::::
# Section

{include VersoTests.DocStructure.Included}

%%%
tag := "late"
%%%
:::::::

/--
error: Metadata already provided for this section
-/
#test_msgs in
#docs (StructuralTesting) duplicateMetadata "Duplicate Metadata" :=
:::::::
%%%
tag := "first"
%%%

%%%
tag := "second"
%%%
:::::::

/--
error: Metadata already provided for this section
-/
#test_msgs in
#docs (StructuralTesting) duplicateMetadataInSection "Duplicate Metadata in a Section" :=
:::::::
# Section
%%%
tag := "first"
%%%

%%%
tag := "second"
%%%
:::::::

/--
error: Block content found in a context where a header was expected.


Note: A document part (section/chapter/etc) consists of a header, followed by zero or more blocks, followed by zero or more sub-parts. This block occurs after a sub-part (namely `VersoTests.DocStructure.Included`), but outside of the sub-parts.
-/
#test_msgs in
#docs (StructuralTesting) contentAfterInclude "Content After an Include" :=
:::::::
Text.

{include VersoTests.DocStructure.Included}

More text.
:::::::

/--
error: Block content found in a context where a header was expected.


Note: A document part (section/chapter/etc) consists of a header, followed by zero or more blocks, followed by zero or more sub-parts. This block occurs after a sub-part (namely `VersoTests.DocStructure.Included`), but outside of the sub-parts.
-/
#test_msgs in
#docs (StructuralTesting) contentAfterIncludeInSection "Content After an Include in a Section" :=
:::::::
# Section

{include 2 VersoTests.DocStructure.Included}

* A list
:::::::

open Lean Lean.Elab Lean.Doc.Syntax Verso.Doc.Elab PartElabM in
/--
Adds a finished part with the title {lit}`Built Part` as a sub-part of the root part. It is an
example of a part command that builds a whole part.
-/
@[part_command Lean.Doc.Syntax.command]
meta def builtPart : PartCommand
  | stx@`(block|command{builtPart $args*}) => do
    unless args.isEmpty do throwErrorAt stx "Expected no arguments"
    let endPos := stx.getTailPos?.getD 0
    closePartsUntil 1 (stx.getPos?.getD 0)
    addPart <| .mk stx stx #[] "Built Part" none #[] #[] endPos
  | _ => throwUnsupportedSyntax

/--
error: Block content found in a context where a header was expected.


Note: A document part (section/chapter/etc) consists of a header, followed by zero or more blocks, followed by zero or more sub-parts. This block occurs after a sub-part (namely “Built Part”), but outside of the sub-parts.
-/
#test_msgs in
#docs (StructuralTesting) contentAfterBuiltPart "Content After a Built Part" :=
:::::::
# Section

{builtPart}

Text.
:::::::

end Verso.Tests.DocStructure.Errors
