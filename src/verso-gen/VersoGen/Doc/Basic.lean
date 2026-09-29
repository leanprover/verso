/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Json.FromToJson

set_option doc.verso true

/-!
Surface documents, which describe Verso documents as authors write them, with the shape of Verso's
concrete syntax. Verso's own document types describe elaborated documents, and surface
documents describe the source that elaboration starts from: the extensions that a document uses
appear by name, and genre-specific content doesn't appear. The generator makes, edits and
concretizes surface documents, and each one describes a document that parses.
-/

namespace VersoGen.Doc.SurfaceDoc

open Lean

/-- Where a link points. -/
public inductive LinkTarget where
  /-- A URL, as in {lit}`[text](url)`. -/
  | url (url : String)
  /-- A link definition, as in {lit}`[text][label]`. -/
  | ref (label : String)
deriving ToJson, FromJson, BEq, Repr, Inhabited

public inductive Inline where
  | text (str : String)
  | emph (content : Array Inline)
  | bold (content : Array Inline)
  | link (content : Array Inline) (target : LinkTarget)
  /--
  A role. Roles whose content is a single inline code element are concretized with the code
  directly after their names and arguments.
  -/
  | role (name args : String) (content : Array Inline)
  | image (alt url : String)
  | code (str : String)
  /-- A footnote use: the label of a footnote definition. -/
  | footnote (label : String)
deriving ToJson, FromJson, BEq, Repr, Inhabited

/--
A block. List items are arrays of blocks, and description list items are terms with arrays of
blocks.
-/
public inductive Block where
  | para (content : Array Inline)
  | ul (items : Array (Array Block))
  | ol (items : Array (Array Block))
  | dl (items : Array (Array Inline × Array Block))
  | blockquote (blocks : Array Block)
  | directive (name args : String) (blocks : Array Block)
  | code (name args : String) (lines : Array String)
  | command (name args : String)
  | linkDef (label url : String)
  | footnoteDef (label : String) (content : Array Inline)
deriving ToJson, FromJson, BEq, Repr, Inhabited

/-- A description list item: its term and its blocks. -/
public abbrev DescItem := Array Inline × Array Block

/-- A part: its title, metadata fields, blocks and sub-parts. The document itself is a part. -/
public structure Part where
  title : String
  /-- The metadata fields, as names and values in Lean source. -/
  metadata : Array (String × String) := #[]
  blocks : Array Block := #[]
  subParts : Array Part := #[]
deriving ToJson, FromJson, BEq, Repr, Inhabited

/--
A part, a block, a list item or a description list item. These are what the zipper focuses on and
what sibling edits insert.
-/
public inductive Node where
  | part (part : Part)
  | block (block : Block)
  | item (blocks : Array Block)
  | descItem (item : DescItem)
deriving ToJson, FromJson, BEq, Repr, Inhabited

namespace Node

/-- The nodes directly in a node. Parts' blocks come before their sub-parts. -/
public def children : Node → Array Node
  | .part p => p.blocks.map .block ++ p.subParts.map .part
  | .block b =>
    match b with
    | .ul items | .ol items => items.map .item
    | .dl items => items.map .descItem
    | .blockquote bs | .directive _ _ bs => bs.map .block
    | _ => #[]
  | .item bs | .descItem (_, bs) => bs.map .block

end Node

/--
The kinds of surface document blocks that a genre profile and the generator's parameters refer to.
-/
public inductive BlockKind where
  | para | ul | ol | dl | blockquote | directive | code | command | linkDef | footnoteDef
deriving ToJson, FromJson, BEq, Repr, Inhabited, DecidableEq

/-- The kinds of surface document blocks other than link and footnote definitions. -/
public def BlockKind.exceptDefinitions : List BlockKind :=
  [.para, .ul, .ol, .dl, .blockquote, .directive, .code, .command]

public def Block.kind : Block → BlockKind
  | .para .. => .para
  | .ul .. => .ul
  | .ol .. => .ol
  | .dl .. => .dl
  | .blockquote .. => .blockquote
  | .directive .. => .directive
  | .code .. => .code
  | .command .. => .command
  | .linkDef .. => .linkDef
  | .footnoteDef .. => .footnoteDef

/-- The blocks directly in a block, through its items for a list. -/
public def Block.innerBlocks : Block → Array Block
  | .ul items | .ol items => items.flatMap id
  | .dl items => items.flatMap (·.2)
  | .blockquote bs | .directive _ _ bs => bs
  | _ => #[]

/-- The number of nodes in a block: itself, its items, and the blocks in them. -/
partial def Block.nodeCount (b : Block) : Nat :=
  let blocks (bs : Array Block) := bs.foldl (· + ·.nodeCount) 0
  1 + match b with
    | .ul items | .ol items => items.foldl (fun n i => n + 1 + blocks i) 0
    | .dl items => items.foldl (fun n i => n + 1 + blocks i.2) 0
    | .blockquote bs | .directive _ _ bs => blocks bs
    | _ => 0

/-- The number of nodes in a part: itself, its blocks, its sub-parts, and the nodes in them. -/
public partial def Part.nodeCount (p : Part) : Nat :=
  1 + p.blocks.foldl (· + ·.nodeCount) 0 + p.subParts.foldl (· + ·.nodeCount) 0

/-- The number of directives on the longest chain of nested directives in the block's blocks. -/
public partial def Block.directiveDepth (b : Block) : Nat := Id.run do
  let mut v := 0
  for c in b.innerBlocks do
    v := Nat.max v <| (if c matches .directive .. then 1 else 0) + c.directiveDepth
  return v

/-- Link labels and footnote labels, latest first. -/
public structure Refs where
  links : Array String := #[]
  footnotes : Array String := #[]
deriving Inhabited

instance : Append Refs where
  append later earlier := {
    links := later.links ++ earlier.links
    footnotes := later.footnotes ++ earlier.footnotes
  }

/-- The labels that {name}`f` gives for the elements of {name}`xs`. -/
def Refs.ofArray (f : α → Refs) (xs : Array α) : Refs :=
  xs.foldl (fun earlier x => f x ++ earlier) {}

/-- The link and footnote labels that an inline uses. -/
partial def Inline.refs : Inline → Refs
  | .text .. | .image .. | .code .. => {}
  | .emph c | .bold c | .role _ _ c => .ofArray Inline.refs c
  | .link c t =>
    let inner := Refs.ofArray Inline.refs c
    match t with
    | .ref n => { inner with links := #[n] ++ inner.links }
    | .url _ => inner
  | .footnote n => { footnotes := #[n] }

/-- The link and footnote labels that a block uses. -/
partial def Block.refs (b : Block) : Refs :=
  match b with
  | .para c | .footnoteDef _ c => .ofArray Inline.refs c
  | .dl items =>
    .ofArray (fun (t, bs) => Refs.ofArray Block.refs bs ++ .ofArray Inline.refs t) items
  | b => .ofArray Block.refs b.innerBlocks

/-- The link and footnote labels that a part uses. -/
public partial def Part.refs (p : Part) : Refs :=
  Refs.ofArray Part.refs p.subParts ++ .ofArray Block.refs p.blocks

/-- The labels of the link and footnote definitions in a block. -/
partial def Block.defs (b : Block) : Refs :=
  match b with
  | .linkDef label _ => { links := #[label] }
  | .footnoteDef label _ => { footnotes := #[label] }
  | b => .ofArray Block.defs b.innerBlocks

/-- The labels of the link and footnote definitions in a part. -/
public partial def Part.defs (p : Part) : Refs :=
  Refs.ofArray Part.defs p.subParts ++ .ofArray Block.defs p.blocks
