/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual.Markdown
import Verso.Doc.Elab.Monad
import Lean.Elab.Term

open Verso Doc Elab
open Verso.Genre Manual
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
  | .mk _ _ title _ _ subParts _ =>
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
      levels ← Markdown.addPartFromMarkdown block levels
    closePartsUntil 0 0
  let (_, _, part) ← addParts.run ⟨Syntax.node .none identKind #[], mkConst ``Manual, .always, .none⟩ default default
  part.partContext.priorParts.toList.map displayPartStructure |> String.join |> pure

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
#guard_msgs in
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
