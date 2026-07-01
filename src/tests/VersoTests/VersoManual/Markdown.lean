/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import VersoManual.Markdown
import Verso.Doc.Elab.Monad
import Lean.Elab.Term

open Verso Doc Elab
open Verso.Genre Manual Markdown
open Lean

/--
Renders the entire structure of a finished part as Markdown-style headings, with a
number of `'#'s` that reflects their nesting depth. This is a tool for debugging/testing
only.

To avoid off-by-one misunderstandings: The heading level is equal to
the number of # characters in the opening sequence. (cf. [CommonMark
Spec](https://spec.commonmark.org/0.31.2/))
-/
def displayPartStructure (part : FinishedPart) (level : Nat := 1) : String := match part with
  | .mk _ _ _ title _ _ subParts _ =>
       let partsStr : String := subParts.map (displayPartStructure · (level + 1))
         |>.toList |> String.join
       let pref := "".pushn '#' level
       s!"{pref} {title}\n{partsStr}"
  | .included name => s!"included {name}\n"

open PartElabM in
/--
Parses a Markdown string, returning the displayed part structure.
-/
def testAddPartFromMarkdown (input : String) : Elab.TermElabM String := do
  let some parsed := MD4Lean.parse input
    | throwError m!"Couldn't parse markdown {input}"
  let addParts : PartElabM Unit := do
    let mut levels := []
    for block in parsed.blocks do
      levels ← addPartFromMarkdown block levels
    closePartsUntil 0 0
  let (_, _, part) ← addParts.run ⟨Syntax.node .none identKind #[], mkConst ``Manual, .always, .none⟩ default default
  part.partContext.priorParts.toList.map displayPartStructure |> String.join |> pure

/--
Every part produced from Markdown headers must have range and selection syntax whose recovered
ranges satisfy the TOC invariant: the selection range lies within `[rangeStart, endPos]`. Violating
it (position-less syntax, or an `endPos` of zero) panics in `requireValidTOCRanges` during the
document-symbol/folding conversion.
-/
partial def partRangesValid : FinishedPart → Bool
  | .mk rangeStx selectionStx _ _ _ _ subParts endPos =>
    match rangeStx.getRange?, selectionStx.getRange? with
    | some r, some sel => (r.start ≤ sel.start) && (sel.stop ≤ endPos) && subParts.all partRangesValid
    | _, _ => false
  | .included _ => true

open PartElabM in
/--
Parses Markdown under a positioned reference and closes the document at that reference's end, as a
real document's Markdown block elaborator would, then reports whether every resulting part has a
valid TOC range.
-/
def markdownPartRangesValid (input : String) : Elab.TermElabM Bool := do
  let some parsed := MD4Lean.parse input
    | throwError m!"Couldn't parse markdown {input}"
  let ref := Syntax.node (.synthetic ⟨0⟩ ⟨100⟩) identKind #[]
  withRef ref do
    let addParts : PartElabM Unit := do
      let mut levels := []
      for block in parsed.blocks do
        levels ← addPartFromMarkdown block levels
      closePartsUntil 0 (ref.getTailPos?.getD default)
    let (_, _, part) ← addParts.run ⟨Syntax.node .none identKind #[], mkConst ``Manual, .always, .none⟩ default default
    return part.partContext.priorParts.all partRangesValid

/-- info: true -/
#test_msgs in
#eval markdownPartRangesValid r#"
# Acknowledgements
## Contributors
# Another Section
"#

/--
info:
# header1
## header2-a
### header3-aa
## header 2-b
### header3-ba
### header3-bb
#### header4-bba
### header3-bc
# another header
## one more
-/
#test_msgs in
/- Exercises how inconsistent Markdown header nesting depth
is heuristically fixed. -/
#eval do
  IO.println <| "\n" ++ (← testAddPartFromMarkdown r#"
# header1
## header2-a
### header3-aa
## header 2-b
##### header3-ba
#### header3-bb
###### header4-bba
### header3-bc
# another header
## one more
"#)
