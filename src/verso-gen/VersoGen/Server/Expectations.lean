/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Lsp.Basic
public import Lean.Data.Lsp.Utf16
public import VersoGen.Doc.Concretize

set_option doc.verso true

/-!
What the language server should report for a generated document when it is opened, derived from
the surface document and its concretized text. The language server checks compare the server's
answers with these expectations.
-/

namespace VersoGen.Server

open VersoGen.Doc VersoGen.Doc.SurfaceDoc VersoGen.Genre

open Lean

/--
The name and the detail of the document symbol of a {lit}`lean` code block or a {lit}`docstring`
command.
-/
public structure CodeSymbol where
  name : String
  detail : String
deriving BEq, Repr, Inhabited

/--
A part's title, the document symbols of the {lit}`lean` code blocks and {lit}`docstring` commands
in its blocks, and the part trees of its sub-parts.
-/
public structure PartTree where
  title : String
  code : Array CodeSymbol
  subParts : Array PartTree
deriving BEq, Repr, Inhabited

/--
The names and details of the document symbols of some blocks, at any depth. The names of the
symbols of {lit}`lean` code blocks come from the blocks' first lines, shortened to 20 characters and
`…`. Their detail is {lit}`Lean code`, with {lit}`(hidden)` for blocks hidden with `-show`. The
names of the symbols of {lit}`docstring` commands come from the commands' arguments, and their
detail is {lit}`Documentation`.
-/
partial def codeSymbols (bs : Array Block) : Array CodeSymbol :=
  bs.flatMap fun b =>
    match b with
    | .code "lean" args lines =>
      let first := lines[0]?.getD ""
      let name := if first.length > 20 then (first.take 20).copy ++ "…" else first
      #[{ name, detail := if args == "-show" then "Lean code (hidden)" else "Lean code" }]
    | .command "docstring" args => #[{ name := args, detail := "Documentation" }]
    | b => codeSymbols b.innerBlocks

public partial def partTree (part : Part) : PartTree :=
  .mk part.title (codeSymbols part.blocks) (part.subParts.map partTree)

/-- A folding range that the language server is expected to report, by lines counted from 0. -/
public structure Fold where
  /-- The range's kind, if it has one. -/
  kind? : Option String := none
  startLine : Nat
  endLine : Nat
  /-- What produces the range, for reports. -/
  source : String
deriving BEq, Repr, Inhabited

/--
The folding ranges of a document, as Verso and Lean report them:
* one for each part that spans more than one line, from its header to the line before its end
* one for each code block, directive, blockquote, list, description list and metadata block, at any
  depth
* one for each list and description list for each of its items, over its lines
* one for the imports and {lit}`open` commands
* one region for each top-level code block, directive, blockquote, list and description list that
  spans more than one line, and for each metadata block
-/
public def expectedFolds (p : GenreProfile) (doc : Part) : Array Fold := Id.run do
  -- The number of lines, counting the empty line after the final line break
  let lineCount := ((concretizeDocument p doc).split '\n').fold (init := 0) fun i _ => i + 1
  let eof := lineCount - 1
  let lineRanges := layout p doc
  let parts := lineRanges.filter fun s => s.node matches .part .. && !s.isMetadata
  let mut out : Array Fold := #[]
  -- Parts, from the header to the line before the start of the next part that isn't in it
  for (s, i) in parts.zipIdx do
    let stop := (parts.extract (i + 1) |>.find? (·.depth ≤ s.depth) |>.map (·.first)).getD eof
    if stop - 1 > s.first then
      out := out.push { startLine := s.first, endLine := stop - 1, source := "part" }
  for s in lineRanges do
    let topLevel := s.topLevel
    if s.isMetadata then
      let region : Fold :=
        { kind? := some "region", startLine := s.first, endLine := s.last, source := "command" }
      out := out.push { startLine := s.first, endLine := s.last, source := "metadata" }
      out := out.push region
      continue
    match s.node with
    | .block (.code ..) | .block (.directive ..) | .block (.blockquote ..) =>
      out := out.push { startLine := s.first, endLine := s.last, source := "syntax" }
      if topLevel && s.first < s.last then
        let region : Fold :=
          { kind? := some "region", startLine := s.first, endLine := s.last, source := "command" }
        out := out.push region
    | .block (.dl _) | .block (.ul _) | .block (.ol _) =>
      out := out.push { startLine := s.first, endLine := s.last, source := "syntax" }
      let list : Fold := { startLine := s.first, endLine := s.last, source := "list" }
      out := out ++ Array.replicate s.node.children.size list
      if topLevel && s.first < s.last then
        let region : Fold :=
          { kind? := some "region", startLine := s.first, endLine := s.last, source := "command" }
        out := out.push region
    | _ => pure ()
  -- The imports and `open` commands
  let headerEnd := (p.header.zipIdx.filter (!·.1.isEmpty)).back?.map (·.2) |>.getD 0
  let imports : Fold :=
    { kind? := some "imports", startLine := 0, endLine := headerEnd, source := "imports" }
  return #[imports] ++ out

/-- A link or footnote label, with the ranges of its definition and uses in a document's text. -/
public structure LabelRanges where
  label : String
  isFootnote : Bool
  definition : Lsp.Range
  uses : Array Lsp.Range
deriving Repr, Inhabited

/-- The positions at which a pattern starts in a text, in order. -/
def matchStarts (text pattern : String) : Array String.Pos.Raw :=
  (String.Slice.Pattern.ToForwardSearcher.toSearcher pattern text.toSlice).fold (init := #[])
    fun starts step =>
      match step with
      | .matched start _ => starts.push start.offset
      | .rejected .. => starts

/--
The definitions and uses of a document's link and footnote labels, found in its concretized text.
-/
public def labelRanges (p : GenreProfile) (doc : Part) : Array LabelRanges := Id.run do
  let text := concretizeDocument p doc
  let fileMap := FileMap.ofString text
  let labelRange (start : String.Pos.Raw) (label : String) : Lsp.Range :=
    ⟨fileMap.utf8PosToLspPos start, fileMap.utf8PosToLspPos (start + label)⟩
  let defs := doc.defs
  let mut out := #[]
  for (labels, isFootnote) in [(defs.links, false), (defs.footnotes, true)] do
    for label in labels.reverse do
      let defOpener := if isFootnote then "[^" else "["
      let useOpener := if isFootnote then "[^" else "]["
      let defStarts := matchStarts text (defOpener ++ label ++ "]:")
      let useStarts :=
        matchStarts text (useOpener ++ label ++ "]") |>.filter (!defStarts.contains ·)
      if let some d := defStarts.back? then
        let definition := labelRange (d + defOpener) label
        let uses := useStarts.map fun u => labelRange (u + useOpener) label
        out := out.push { label, isFootnote, definition, uses }
  return out
