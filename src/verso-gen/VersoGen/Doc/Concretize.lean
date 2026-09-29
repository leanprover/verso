/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.Genre.Basic

set_option doc.verso true

/-!
Concretization turns a surface document into the text of a Lean module. Concretization also reports
the lines of the text that each node occupies.
-/

namespace VersoGen.Doc

open SurfaceDoc VersoGen.Genre

mutual
  partial def concretizeInline : Inline → String
    | .text s => s
    | .emph c => "_" ++ concretizeInlines c ++ "_"
    | .bold c => "*" ++ concretizeInlines c ++ "*"
    | .link c (.url u) => "[" ++ concretizeInlines c ++ "](" ++ u ++ ")"
    | .link c (.ref n) => "[" ++ concretizeInlines c ++ "][" ++ n ++ "]"
    | .role name args c =>
      let head := "{" ++ (if args.isEmpty then name else name ++ " " ++ args) ++ "}"
      match c with
      | #[.code s] => head ++ "`" ++ s ++ "`"
      | _ => head ++ "[" ++ concretizeInlines c ++ "]"
    | .image alt url => "![" ++ alt ++ "](" ++ url ++ ")"
    | .code s => "`" ++ s ++ "`"
    | .footnote n => "[^" ++ n ++ "]"

  /-- Concretizes inlines, separated by spaces. -/
  partial def concretizeInlines (xs : Array Inline) : String := Id.run do
    let mut out := ""
    for x in xs, i in [0:xs.size] do
      if i > 0 then out := out ++ " "
      out := out ++ concretizeInline x
    return out
end

/-- The length of the sequence of back-ticks that starts a line, after its leading spaces. -/
def leadingBackticks (line : String) : Nat :=
  ((line.dropWhile (· == ' ')).takeWhile (· == '`')).positions.length

/-- The length of the fences of a code block with the given lines. -/
def fenceLength (lines : Array String) : Nat :=
  lines.foldl (fun acc l => Nat.max acc (leadingBackticks l + 1)) 3

/-- The number of colons in a directive's delimiters. -/
def delimiterLength (b : Block) : Nat := 3 + b.directiveDepth

/--
Which of some sibling blocks are lists that use the other marker. Lists use the other marker when
they follow a list of the same kind that uses the usual one.
-/
def otherMarkers (bs : Array Block) : Array Bool := Id.run do
  let mut out := #[]
  let mut prev? : Option BlockKind := none
  let mut prevOther := false
  for b in bs do
    let other := match prev?, b.kind with
      | some .ul, .ul | some .ol, .ol => !prevOther
      | _, _ => false
    out := out.push other
    prev? := some b.kind
    prevOther := other
  return out

/--
The range of lines that a node's text occupies in the concretized text, with the node's depth.
Parts' metadata blocks have ranges of their own.
-/
public structure LineRange where
  node : Node
  /-- The first line, counted from 0. For a part, this is its header, or the `#doc` line. -/
  first : Nat
  /-- The last line, counted from 0. -/
  last : Nat
  /-- The node's depth: 0 for the document and one more for each enclosing node. -/
  depth : Nat
  /-- Whether the line range is a part's metadata block rather than the node. -/
  isMetadata : Bool := false
  /-- Whether the node is a top-level block: a block directly in a part. -/
  topLevel : Bool := false
deriving Inhabited

/-- The lines of a concretized text and the line ranges of its nodes, in document order. -/
structure Concretized where
  lines : Array String := #[]
  ranges : Array LineRange := #[]

/--
The monad of concretization. Its state is the lines emitted so far and the line ranges recorded for
them.
-/
abbrev ConcretizeM := StateM Concretized

def emit (line : String) : ConcretizeM Unit :=
  modify fun c => { c with lines := c.lines.push line }

def lineCount : ConcretizeM Nat := return (← get).lines.size

/--
Emits a node's lines with {name}`act` and records the node's line range, which spans the lines that
{name}`act` emits. The range comes before the ranges that {name}`act` records.
-/
def recordRange (node : Node) (depth : Nat) (act : ConcretizeM Unit)
    (isMetadata topLevel : Bool := false) : ConcretizeM Unit := do
  let first ← lineCount
  let index := (← get).ranges.size
  modify fun c =>
    { c with ranges := c.ranges.push { node, first, last := first, depth, isMetadata, topLevel } }
  act
  let last := (← lineCount) - 1
  modify fun c => { c with ranges := c.ranges.modify index ({ · with last }) }

/--
Emits groups of lines, with a blank line before each group that follows lines of the earlier
groups.
-/
def separated (groups : Array (ConcretizeM Unit)) : ConcretizeM Unit := do
  let start ← lineCount
  for g in groups do
    if (← lineCount) > start then emit ""
    g

mutual
  /--
  Concretizes a block at {name}`depth`, recording the line ranges of the block and of the blocks in
  it. The first line starts with {name}`first`, and the other lines that aren't empty start with
  {name}`rest`. With {name}`otherMarker`, a list uses {lit}`-` or {lit}`1)` as its marker.
  -/
  partial def concretizeBlock (first rest : String) (depth : Nat) (b : Block)
      (otherMarker topLevel : Bool := false) : ConcretizeM Unit :=
    recordRange (.block b) depth (topLevel := topLevel) do
      match b with
      | .para c => emit (first ++ concretizeInlines c)
      | .ul items =>
        concretizeItems first rest depth (fun _ => if otherMarker then "-" else "*") items
      | .ol items =>
        concretizeItems first rest depth
          (fun i => s!"{i + 1}" ++ if otherMarker then ")" else ".") items
      | .dl items =>
        separated <| items.mapIdx fun i (term, bs) => do
          emit ((if i == 0 then first else rest) ++ ": " ++ concretizeInlines term)
          emit ""
          concretizeBlocks (rest ++ "  ") (rest ++ "  ") (depth + 2) bs
      | .blockquote bs => concretizeBlocks (first ++ "> ") (rest ++ "  ") (depth + 1) bs
      | .directive name args bs =>
        let delim := "".pushn ':' (delimiterLength b)
        emit (first ++ delim ++ if args.isEmpty then name else name ++ " " ++ args)
        concretizeBlocks rest rest (depth + 1) bs
        emit (rest ++ delim)
      | .code name args lines =>
        let fence := "".pushn '`' (fenceLength lines)
        emit (first ++ fence ++ if args.isEmpty then name else name ++ " " ++ args)
        for line in lines do
          emit (if line.isEmpty then line else rest ++ line)
        emit (rest ++ fence)
      | .command name args =>
        emit (first ++ "{" ++ (if args.isEmpty then name else name ++ " " ++ args) ++ "}")
      | .linkDef label url => emit (first ++ "[" ++ label ++ "]: " ++ url)
      | .footnoteDef label c => emit (first ++ "[^" ++ label ++ "]: " ++ concretizeInlines c)

  /--
  Concretizes blocks at {name}`depth`, separated by blank lines. The first line starts with
  {name}`first`, and the other lines that aren't empty start with {name}`rest`.
  -/
  partial def concretizeBlocks (first rest : String) (depth : Nat) (bs : Array Block) :
      ConcretizeM Unit :=
    separated <| (bs.zip (otherMarkers bs)).mapIdx fun i (b, other) =>
      concretizeBlock (if i == 0 then first else rest) rest depth b other

  /-- Concretizes the items of a list at {name}`depth`, each with its marker. -/
  partial def concretizeItems (first rest : String) (depth : Nat) (marker : Nat → String)
      (items : Array (Array Block)) : ConcretizeM Unit :=
    separated <| items.mapIdx fun i bs =>
      let m := marker i ++ " "
      concretizeBlocks ((if i == 0 then first else rest) ++ m) (rest.pushn ' ' m.length)
        (depth + 2) bs
end

/--
The actions that concretize the metadata, the blocks and the sub-parts of a part at {name}`depth`,
one for each group of lines. Each action records the line ranges of the nodes that it emits. A
part's own line range is only its header.
-/
partial def partBody (depth : Nat) (part : Part) : Array (ConcretizeM Unit) :=
  (if part.metadata.isEmpty then #[] else #[metadata]) ++
  (part.blocks.zip (otherMarkers part.blocks)).map
    (fun (b, other) => concretizeBlock "" "" (depth + 1) b other (topLevel := true)) ++
  part.subParts.map fun sub =>
    let header := "".pushn '#' (depth + 1) ++ " " ++ sub.title
    separated <| #[recordRange (.part sub) (depth + 1) (emit header)] ++ partBody (depth + 1) sub
where
  metadata : ConcretizeM Unit :=
    recordRange (.part part) depth (isMetadata := true) do
      emit "%%%"
      for (f, v) in part.metadata do emit (f ++ " := " ++ v)
      emit "%%%"

/-- Concretizes a document into its lines and the line ranges of its nodes. -/
def concretize (p : GenreProfile) (doc : Part) : Concretized :=
  let act : ConcretizeM Unit := do
    for line in p.header do emit line
    recordRange (.part doc) 0 (emit (p.docLine doc.title))
    emit ""
    separated (partBody 0 doc)
  (act.run {}).2

/--
Concretizes a document: the imports and options of the profile, the {lit}`#doc` line and the
document's body.
-/
public def concretizeDocument (p : GenreProfile) (doc : Part) : String := Id.run do
  let mut out := ""
  for line in (concretize p doc).lines do
    out := out ++ line ++ "\n"
  return out

/-! # Layout -/

/-- The line ranges of a document's parts and nodes in its concretized text, in document order. -/
public def layout (p : GenreProfile) (doc : Part) : Array LineRange :=
  (concretize p doc).ranges
