/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso

set_option doc.verso true

/-!
A minimal genre for the document structure tests, and a text rendering of a document's parts.
-/

namespace Verso.Tests.DocStructure

open Verso.Doc

/-- The part metadata of the test genre. -/
public structure StructuralTesting.Metadata where
  tag : String := ""
  number : Nat := 0
deriving Repr

/-- A genre whose only feature is its part metadata. -/
@[expose]
public def StructuralTesting : Genre where
  PartMetadata := StructuralTesting.Metadata
  Block := Empty
  Inline := Empty
  TraverseContext := Unit
  TraverseState := Unit

public instance : Repr (Genre.PartMetadata StructuralTesting) :=
  inferInstanceAs (Repr StructuralTesting.Metadata)

/-- A plain-text summary of some inline content. -/
partial def inlineSummary : Inline StructuralTesting → String
  | .text s | .code s | .math _ s => s
  | .linebreak _ => " "
  | .emph xs | .bold xs | .concat xs => String.join (xs.map inlineSummary).toList
  | .link xs url => s!"[{String.join (xs.map inlineSummary).toList}]({url})"
  | .footnote name _ => s!"[^{name}]"
  | .image alt url => s!"![{alt}]({url})"
  | .other e _ => nomatch e

/-- A one-line summary of a block. -/
def blockSummary : Block StructuralTesting → String
  | .para xs => s!"para: {(String.join (xs.map inlineSummary).toList).trimAscii}"
  | .code s => s!"code: {s.trimAscii}"
  | .ul items => s!"ul: {items.size} items"
  | .ol _ items => s!"ol: {items.size} items"
  | .dl items => s!"dl: {items.size} items"
  | .blockquote items => s!"blockquote: {items.size} blocks"
  | .concat items => s!"concat: {items.size} blocks"
  | .other e _ => nomatch e

/--
Renders a part as indented text: its title, metadata, blocks and sub-parts. Included documents
appear as the parts they contain.
-/
public partial def renderPart (part : Part StructuralTesting) (depth : Nat := 0) : String :=
  let indent := "".pushn ' ' (2 * depth)
  let header := s!"{indent}part {part.titleString.quote}\n"
  let metadata :=
    match part.metadata with
    | some m => s!"{indent}  metadata: {reprStr m}\n"
    | none => ""
  let blocks :=
    s!"{indent}  blocks: {part.content.size}\n" ++
    String.join (part.content.map (s!"{indent}  - {blockSummary ·}\n")).toList
  let subParts := String.join (part.subParts.map (renderPart · (depth + 1))).toList
  header ++ metadata ++ blocks ++ subParts

end Verso.Tests.DocStructure
