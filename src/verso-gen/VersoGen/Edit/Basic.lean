/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.Edit.Generate
public import VersoGen.Doc.Zipper
public import VersoGen.Doc.Concretize

set_option doc.verso true

/-!
Surface document edits, which the edit generator chooses and edit scripts record. Edits apply at
the zipper's focus and determine where they leave the zipper, so that an edit pass can continue
from there. Each kind of node has its own family of edits, and sibling edits change the nodes around
the focus. The edit generator makes only edits that keep the surface document valid for the genre
profile.
-/

namespace VersoGen.Edit

open VersoGen.Doc VersoGen.Doc.SurfaceDoc VersoGen.Genre VersoGen.Random VersoGen.Text

open Lean

/-- An edit of a part's title or metadata. -/
public inductive PartEdit where
  | setTitle (title : String)
  | addMetadata (field value : String)
  | removeMetadata (field : String)
  /-- Changes the value of a metadata field. -/
  | changeMetadata (field value : String)
  /-- Adds {name}`count` empty sub-parts, without a title, after the others. -/
  | addSubParts (count : Nat)
deriving ToJson, FromJson, BEq, Repr, Inhabited

/--
An edit of inlines: a paragraph's content, a description list item's term, or a footnote
definition's content.
-/
public inductive InlineEdit where
  /--
  Replaces {name}`count` words, from word {name}`start`, of the text inline at {name}`index` with
  {name}`text`.
  -/
  | editText (index start count : Nat) (text : String)
  | insertInline (index : Nat) (inline : Inline)
  | removeInline (index : Nat)
  /--
  Puts the inlines from {name}`start` up to {name}`stop` inside {name}`wrapper`, whose own content
  is ignored.
  -/
  | wrapInlines (start stop : Nat) (wrapper : Inline)
  /-- Replaces an emphasis, bold, link or role with its content. -/
  | unwrapInline (index : Nat)
deriving ToJson, FromJson, BEq, Repr, Inhabited

/-- A new name and arguments for a directive. -/
public structure DirectiveEdit where
  name : String
  args : String
deriving ToJson, FromJson, BEq, Repr, Inhabited

/-- New arguments for a block command. -/
public structure CommandEdit where
  args : String
deriving ToJson, FromJson, BEq, Repr, Inhabited

/-- A new URL for a link definition. -/
public structure LinkDefEdit where
  url : String
deriving ToJson, FromJson, BEq, Repr, Inhabited

/-- New content for a footnote definition. -/
public structure FootnoteDefEdit where
  content : Array Inline
deriving ToJson, FromJson, BEq, Repr, Inhabited

/-- Where a reference edit puts the definition. -/
public inductive DefinitionPlace where
  /-- Just before the top-level block that contains the use. -/
  | beforeBlock
  /-- Just after the top-level block that contains the use. -/
  | afterBlock
  /-- After the blocks of the last part, at the end of the document. -/
  | documentEnd
deriving ToJson, FromJson, BEq, Repr, Inhabited

/-- An edit that inserts a link or footnote use into a paragraph, together with its definition. -/
public structure ReferenceEdit where
  /-- Where the use goes among the paragraph's inlines. -/
  index : Nat
  /-- The use: a link or a footnote with the definition's label. -/
  use : Inline
  /-- The definition of the use's label. -/
  definition : Block
  place : DefinitionPlace
deriving ToJson, FromJson, BEq, Repr, Inhabited

/-- What a sequence of siblings is wrapped in: a new part for parts, or a new block for blocks. -/
public inductive Container where
  | part (title : String)
  | blockquote
  /-- A list with one item, which contains the blocks. -/
  | ul
  /-- A numbered list with one item, which contains the blocks. -/
  | ol
  | directive (name args : String)
deriving ToJson, FromJson, BEq, Repr, Inhabited

/--
An edit of the focus as one of its parent's children. The indices count those children from the
focus, so index 0 is the focus itself.
-/
public inductive SiblingEdit where
  /-- Inserts a node before the node at {name}`index`. At index 1, it follows the focus. -/
  | insert (index : Nat) (node : Node)
  /-- Deletes a node. At index 0, the focus is deleted. -/
  | delete (index : Nat)
  /-- Puts the nodes from {name}`start` up to {name}`stop` inside a new container. -/
  | wrap (start stop : Nat) (container : Container)
  /--
  Moves a node's contents out into its parent. If the node is a block, the blocks in it replace it.
  If it is a part, it keeps its blocks, and its sub-parts follow it.
  -/
  | deparent (index : Nat)
  /-- Moves the node after the node at {name}`index` to the end of the node at {name}`index`. -/
  | reparent (index : Nat)
deriving ToJson, FromJson, BEq, Repr, Inhabited

/-- An edit at the zipper's focus, from one of the edit families. Edit scripts record these. -/
public inductive Edit where
  | part (edit : PartEdit)
  | inlines (edit : InlineEdit)
  | directive (edit : DirectiveEdit)
  | command (edit : CommandEdit)
  | code (edit : LineEdit)
  | linkDef (edit : LinkDefEdit)
  | footnoteDef (edit : FootnoteDefEdit)
  | reference (edit : ReferenceEdit)
  | sibling (edit : SiblingEdit)
  /--
  An edit of the focus's children, as {name}`SiblingEdit` describes for the children of the focus's
  parent, with indices from the focus's first child.
  -/
  | contents (edit : SiblingEdit)
deriving ToJson, FromJson, BEq, Repr, Inhabited

namespace Edit

public def setTitle (title : String) : Edit := .part (.setTitle title)

public def addMetadata (field value : String) : Edit := .part (.addMetadata field value)

public def removeMetadata (field : String) : Edit := .part (.removeMetadata field)

public def changeMetadata (field value : String) : Edit := .part (.changeMetadata field value)

public def addSubParts (count : Nat) : Edit := .part (.addSubParts count)

public def insertSibling (index : Nat) (node : Node) : Edit := .sibling (.insert index node)

public def deleteSibling (index : Nat) : Edit := .sibling (.delete index)

public def wrap (start stop : Nat) (container : Container) : Edit :=
  .sibling (.wrap start stop container)

public def deparent (index : Nat) : Edit := .sibling (.deparent index)

public def reparent (index : Nat) : Edit := .sibling (.reparent index)

public def changeDirective (name args : String) : Edit := .directive { name, args }

public def changeCommandArgs (args : String) : Edit := .command { args }

public def editText (index start count : Nat) (text : String) : Edit :=
  .inlines (.editText index start count text)

public def insertInline (index : Nat) (inline : Inline) : Edit :=
  .inlines (.insertInline index inline)

public def removeInline (index : Nat) : Edit := .inlines (.removeInline index)

public def wrapInlines (start stop : Nat) (wrapper : Inline) : Edit :=
  .inlines (.wrapInlines start stop wrapper)

public def unwrapInline (index : Nat) : Edit := .inlines (.unwrapInline index)

public def changeLines (edit : LineEdit) : Edit := .code edit

public def changeLinkDef (url : String) : Edit := .linkDef { url }

public def changeFootnoteDef (content : Array Inline) : Edit := .footnoteDef { content }

end Edit

def replaceRange (a : Array α) (start stop : Nat) (xs : Array α) : Array α :=
  a.extract 0 start ++ xs ++ a.extract stop

def PartEdit.apply (part : Part) : PartEdit → Option Part
  | .setTitle t => some { part with title := t }
  | .addMetadata f v => do
    guard (!part.metadata.any (·.1 == f))
    some { part with metadata := part.metadata.push (f, v) }
  | .removeMetadata f => do
    guard (part.metadata.any (·.1 == f))
    some { part with metadata := part.metadata.filter (·.1 != f) }
  | .changeMetadata f v => do
    guard (part.metadata.any (·.1 == f))
    some { part with metadata := part.metadata.map fun (f', v') => (f', if f' == f then v else v') }
  | .addSubParts n =>
    some { part with subParts := part.subParts ++ Array.replicate n { title := "" } }

def InlineEdit.apply (c : Array Inline) : InlineEdit → Option (Array Inline)
  | .editText i start count text => do
    let .text s ← c[i]? | none
    let size := (s.split ' ').length
    guard (start + count ≤ size)
    let words := Id.run do
      let mut words : Array String.Slice := #[]
      let mut k := 0
      for w in s.split ' ' do
        if k == start && !text.isEmpty then words := words.push text.toSlice
        if k < start || start + count ≤ k then words := words.push w
        k := k + 1
      if start == size && !text.isEmpty then words := words.push text.toSlice
      return words
    if words.isEmpty then some (c.eraseIdxIfInBounds i)
    else
      let out := Id.run do
        let mut out := ""
        for w in words, j in [0:words.size] do
          if j > 0 then out := out ++ " "
          out := out ++ w
        return out
      some (c.set! i (.text out))
  | .insertInline i inl => do
    guard (i ≤ c.size)
    some (replaceRange c i i #[inl])
  | .removeInline i => do
    guard (i < c.size)
    some (c.eraseIdxIfInBounds i)
  | .wrapInlines start stop w => do
    guard (start < stop && stop ≤ c.size)
    let wrapped := c.extract start stop
    let w ← match w with
      | .emph _ => some (Inline.emph wrapped)
      | .bold _ => some (.bold wrapped)
      | .link _ t => some (.link wrapped t)
      | .role n a _ => some (.role n a wrapped)
      | _ => none
    some (replaceRange c start stop #[w])
  | .unwrapInline i => do
    let inner ← match c[i]? with
      | some (.emph x) | some (.bold x) | some (.link x _) | some (.role _ _ x) => some x
      | _ => none
    some (replaceRange c i (i + 1) inner)

/-- Applies an edit of a node's own contents, giving the edited node. -/
def Edit.applyToNode (e : Edit) (n : Node) : Option Node :=
  match e, n with
  | .part e, .part pt => (.part ·) <$> e.apply pt
  | .inlines e, .block (.para c) => (.block <| .para ·) <$> e.apply c
  | .inlines e, .block (.footnoteDef label c) => (.block <| .footnoteDef label ·) <$> e.apply c
  | .inlines e, .descItem (term, bs) => (fun t => .descItem (t, bs)) <$> e.apply term
  | .directive e, .block (.directive _ _ bs) => some (.block (.directive e.name e.args bs))
  | .command e, .block (.command name _) => some (.block (.command name e.args))
  | .code le, .block (.code name args lines) => do
    guard (le.start + le.count ≤ lines.size)
    some (.block (.code name args (replaceRange lines le.start (le.start + le.count) le.lines)))
  | .linkDef e, .block (.linkDef label _) => some (.block (.linkDef label e.url))
  | .footnoteDef e, .block (.footnoteDef label _) => some (.block (.footnoteDef label e.content))
  | _, _ => none

/-- The blocks among some nodes, or {name}`none` if one isn't a block. -/
def blocksOf? (ns : Array Node) : Option (Array Block) :=
  ns.mapM fun | .block b => some b | _ => none

/-- The parts among some nodes, or {name}`none` if one isn't a part. -/
def partsOf? (ns : Array Node) : Option (Array Part) :=
  ns.mapM fun | .part p => some p | _ => none

/--
The node with {name}`cs` as its children, or {name}`none` if they don't fit. If the node is a part,
the children must be its blocks followed by its sub-parts.
-/
def _root_.VersoGen.Doc.SurfaceDoc.Node.withChildren? (n : Node) (cs : Array Node) : Option Node :=
  match n with
  | .part p => do
    let blocks := cs.takeWhile (· matches .block ..)
    let subParts ← partsOf? (cs.extract blocks.size)
    some (.part { p with blocks := ← blocksOf? blocks, subParts })
  | .block b =>
    match b with
    | .ul _ => (.block <| .ul ·) <$> cs.mapM fun | .item i => some i | _ => none
    | .ol _ => (.block <| .ol ·) <$> cs.mapM fun | .item i => some i | _ => none
    | .dl _ => (.block <| .dl ·) <$> cs.mapM fun | .descItem i => some i | _ => none
    | .blockquote _ => (.block <| .blockquote ·) <$> blocksOf? cs
    | .directive name args _ => (.block <| .directive name args ·) <$> blocksOf? cs
    | _ => none
  | .item _ => .item <$> blocksOf? cs
  | .descItem (term, _) => (fun bs => .descItem (term, bs)) <$> blocksOf? cs

/-- The node that a container makes of some nodes. -/
def Container.wrap (k : Container) (ns : Array Node) : Option Node :=
  match k with
  | .part title => do
    let subParts ← partsOf? ns
    some (.part { title, subParts })
  | .blockquote => (.block <| .blockquote ·) <$> blocksOf? ns
  | .ul => (fun bs => .block (.ul #[bs])) <$> blocksOf? ns
  | .ol => (fun bs => .block (.ol #[bs])) <$> blocksOf? ns
  | .directive name args => (.block <| .directive name args ·) <$> blocksOf? ns

/--
The blocks of a block that is a container, which replace the container when a deparent edit removes
it.
-/
def blockContent : Block → Option (Array Block)
  | .directive _ _ bs | .blockquote bs => some bs
  | .ul items | .ol items => some (items.flatMap id)
  | .dl items => some (items.flatMap (·.2))
  | _ => none

/--
Adds {name}`c` at the end of the blocks of {name}`b`, which for a list are the blocks of its last
item.
-/
def appendBlock (b c : Block) : Option Block :=
  match b with
  | .directive name args bs => some (.directive name args (bs.push c))
  | .blockquote bs => some (.blockquote (bs.push c))
  | .ul items => items.back?.map fun last => .ul (items.pop.push (last.push c))
  | .ol items => items.back?.map fun last => .ol (items.pop.push (last.push c))
  | .dl items => items.back?.map fun (term, bs) => .dl (items.pop.push (term, bs.push c))
  | _ => none

/--
Applies a sibling edit to the children of a node. The indices count the children from the first
one.
-/
def SiblingEdit.apply (parent : Node) (e : SiblingEdit) : Option Node := do
  let cs := parent.children
  let cs ← match e with
    | .insert i c => do
      guard (i ≤ cs.size)
      some (replaceRange cs i i #[c])
    | .delete i => do
      guard (i < cs.size)
      some (cs.eraseIdxIfInBounds i)
    | .wrap start stop k => do
      guard (start < stop && stop ≤ cs.size)
      some (replaceRange cs start stop #[← k.wrap (cs.extract start stop)])
    | .deparent i => do
      let replacement ← match ← cs[i]? with
        | .part c => do
          guard (!c.subParts.isEmpty)
          some (#[Node.part { c with subParts := #[] }] ++ c.subParts.map .part)
        | .block b => (·.map .block) <$> blockContent b
        | _ => none
      some (replaceRange cs i (i + 1) replacement)
    | .reparent i => do
      let c' ← match ← cs[i]?, ← cs[i + 1]? with
        | .part c, .part d => some (.part { c with subParts := c.subParts.push d })
        | .part c, .block d => do
          guard c.subParts.isEmpty
          some (.part { c with blocks := c.blocks.push d })
        | .block b, .block d => (.block ·) <$> appendBlock b d
        | _, _ => none
      some (replaceRange cs i (i + 2) #[c'])
  parent.withChildren? cs

/-- Adds {name}`i` to the indices of a sibling edit. -/
def SiblingEdit.shift (i : Nat) : SiblingEdit → SiblingEdit
  | .insert j c => .insert (i + j) c
  | .delete j => .delete (i + j)
  | .wrap start stop k => .wrap (i + start) (i + stop) k
  | .deparent j => .deparent (i + j)
  | .reparent j => .reparent (i + j)

/--
Moves the zipper from a node after a sibling edit changed the node's children, so that
{name}`Zipper.next?` goes where the traversal continues. The edit's indices count the children from
the first one.
* After an insertion, the zipper is at the new node. After an insertion before the focus, the
  traversal visits the new node's contents and then the former focus again.
* After a wrap, it is at the new container, so the traversal continues with the wrapped nodes.
* After a deletion or the deparent of a block, it is before the node at the edited index, so the
  traversal visits that node.
* After the deparent of a part, it is at the part, whose blocks come next.
* After a reparent, it is before the moved node.
-/
def SiblingEdit.reposition (e : SiblingEdit) (z : Zipper) : Zipper :=
  let before (j : Nat) : Zipper :=
    match j with
    | 0 => z
    | j + 1 => ((z.child? j).map Zipper.lastDescendant).getD z
  match e with
  | .insert j _ | .wrap j _ _ => (z.child? j).getD z
  | .delete j => before j
  | .deparent j =>
    match z.child? j with
    | some c => if c.focus matches .part .. then c else before j
    | none => before j
  | .reparent j =>
    match (z.child? j).bind Zipper.lastChild? with
    | some m =>
      let m := if m.focus matches .item .. | .descItem .. then m.lastChild?.getD m else m
      m.prev?.getD m
    | none => before j

/-- The path of the top-level block that contains the node at {name}`path`, in a document. -/
def partBlockPath? (doc : Part) (path : List Nat) : Option (List Nat) :=
  (List.range path.length).reverse.findSome? fun k => do
    let z ← Zipper.goto doc (path.take k)
    guard (z.focus matches .part ..)
    some (path.take (k + 1))

/-- The path of the last part of a document in document order, which ends the document. -/
partial def lastPartPath (part : Part) : List Nat :=
  match part.subParts.back? with
  | some last => (part.blocks.size + part.subParts.size - 1) :: lastPartPath last
  | none => []

/-- Inserts a node into the node at {name}`path`, before its child at {name}`index`. -/
def insertAt? (doc : Part) (path : List Nat) (index : Nat) (n : Node) : Option Part := do
  let z ← Zipper.goto doc path
  let z ← z.replaceFocus? (← (SiblingEdit.insert index n).apply z.focus)
  some z.root

/--
Applies a reference edit to a focused paragraph. The use goes among the paragraph's inlines, and the
definition goes where the edit says. The zipper stays at the paragraph.
-/
def ReferenceEdit.apply (e : ReferenceEdit) (z : Zipper) : Option Zipper := do
  let .block (.para c) := z.focus | none
  guard (e.index ≤ c.size)
  let z ← z.replaceFocus? (.block (.para (replaceRange c e.index e.index #[e.use])))
  let path := z.indexPath
  let blockPath ← partBlockPath? z.root path
  let partPath := blockPath.dropLast
  let blockIndex ← blockPath.getLast?
  let definition := Node.block e.definition
  let (doc, path) ← match e.place with
    | .beforeBlock =>
      (·, path.modify (partPath.length) (· + 1)) <$> insertAt? z.root partPath blockIndex definition
    | .afterBlock => (·, path) <$> insertAt? z.root partPath (blockIndex + 1) definition
    | .documentEnd =>
      let lastPath := lastPartPath z.root
      let last ← Zipper.goto z.root lastPath
      let .part lastPart := last.focus | none
      (·, path) <$> insertAt? z.root lastPath lastPart.blocks.size definition
  Zipper.goto doc path

/--
Applies an edit at the zipper's focus. Edits of the focus's contents and reference edits leave the
zipper at the focus. Sibling edits apply to the focus's parent, and the zipper then moves as
{name}`SiblingEdit.reposition` describes.
-/
public def Edit.apply (e : Edit) (z : Zipper) : Option Zipper := do
  match e with
  | .sibling e =>
    let parent ← z.up?
    let e := e.shift z.indexInParent
    let parent ← parent.replaceFocus? (← e.apply parent.focus)
    some (e.reposition parent)
  | .contents e => z.replaceFocus? (← e.apply z.focus)
  | .reference e => e.apply z
  | e => z.replaceFocus? (← e.applyToNode z.focus)

/-- Applies an edit as {name}`Edit.apply` does, if the edited surface document is valid. -/
public def applyEdit (p : GenreProfile) (e : Edit) (z : Zipper) : Option Zipper := do
  let z' ← e.apply z
  guard (p.valid z'.root)
  some z'

/--
The position of the first character at which the concretized texts of two surface documents differ.
-/
public def firstChange (p : GenreProfile) (before after : Part) : String.Pos.Raw :=
  (concretizeDocument p before).firstDiffPos (concretizeDocument p after)

/-! # Candidate Edits -/

open Plausible

/-- A random index below {name}`len`, or {name}`none` if {name}`len` is zero. -/
private def index? (len : Nat) : Gen (Option Nat) :=
  if h : 0 < len then (some ·.val) <$> Gen.chooseNatLt 0 len h else pure none

/--
A new block to insert, of a kind from the parameters' mix for top-level blocks or for blocks in
containers. Its inlines have no link or footnote uses.
-/
public def newBlock (p : GenreProfile) (params : Params) (inDirective topLevel : Bool) :
    LoremGen Block := do
  let g ← genBlock p { params with directiveDepth := if inDirective then 2 else 1 }
    (if inDirective then 1 else 0) (if topLevel then 0 else 1) BlockKind.exceptDefinitions
    (refs := false)
  return g.block

/-- A new paragraph. Its inlines have no link or footnote uses. -/
def newParagraph (p : GenreProfile) (params : Params) : LoremGen Block := do
  return .para (← genInlines p params false).1

/-- A new container for wrapping blocks. -/
def newContainer (p : GenreProfile) (inDirective : Bool) : LoremGen Container := do
  let dirs := usableDirectives p inDirective
  match (← Gen.choose Nat 0 (if dirs.isEmpty then 2 else 4) (Nat.zero_le _)).val with
  | 0 => return .blockquote
  | 1 => return .ul
  | 2 => return .ol
  | _ =>
    if h : dirs = [] then return .blockquote else
    let d ← Gen.elements dirs (List.length_pos_iff.mpr h)
    return .directive d.name (← d.args)

/-- The sibling edits of the focus. -/
def siblingEdits (p : GenreProfile) (params : Params) (z : Zipper) :
    List (LoremGen (Option Edit)) :=
  match z.up? with
  | none => []
  | some parent =>
    let n := z.focus
    let inDir := z.inDirective
    let inPart := parent.focus matches .part ..
    let right := parent.focus.children.extract (z.indexInParent + 1)
    -- Where an insertion goes: before the focus (0) or after it (1).
    let beforeOrAfter : LoremGen Nat := do return (← Gen.choose Nat 0 1 (by decide)).val
    -- The number of nodes in a sequence that starts at the focus.
    let sequenceLength (same : Node → Bool) : LoremGen Nat := do
      let longest := Nat.min 3 (1 + (right.takeWhile same).size)
      return (← Gen.choose Nat 1 (Nat.max 1 longest) (Nat.le_max_left ..)).val
    let isPart (n : Node) : Bool := n matches .part ..
    let isBlock (n : Node) : Bool := n matches .block ..
    match parent.focus with
    | .block (.ul ..) | .block (.ol ..) | .block (.dl ..) =>
      [ -- Insert an item before or after the focus.
        do
          let para ← newParagraph p params
          let term := (bareWord (← Lorem.word)).capitalize
          let item : Node := match parent.focus with
            | .block (.dl ..) =>
              .descItem (#[.text (if term.isEmpty then "Lorem" else term)], #[para])
            | _ => .item #[para]
          return some (.insertSibling (← beforeOrAfter) item),
        -- Delete the focus.
        do return some (.deleteSibling 0)
      ]
    | _ =>
      [ -- Delete the focus.
        do return some (.deleteSibling 0),
        -- Deparent the focus.
        do return some (.deparent 0),
        -- Reparent the next sibling into the focus.
        do return some (.reparent 0)
      ] ++
      if isPart n then
        [ -- Insert a part before or after the focus.
          do
            let part : Part := { title := ← Lorem.title, blocks := #[← newParagraph p params] }
            return some (.insertSibling (← beforeOrAfter) (.part part)),
          -- Wrap a sequence of parts in a new part.
          do return some (.wrap 0 (← sequenceLength isPart) (.part (← Lorem.title)))
        ]
      else
        [ -- Insert a block before or after the focus.
          do
            let block ← newBlock p params inDir inPart
            return some (.insertSibling (← beforeOrAfter) (.block block)),
          -- Wrap a sequence of blocks in a new container.
          do return some (.wrap 0 (← sequenceLength isBlock) (← newContainer p inDir)),
          -- Insert a link definition before or after the focus.
          do
            if !p.linkDefs || !inPart then return none
            let url := s!"https://example.com/{bareWord (← Lorem.word)}"
            return some (.insertSibling (← beforeOrAfter) (.block (.linkDef (← Lorem.label) url))),
          -- Insert a footnote definition before or after the focus.
          do
            if !p.footnoteDefs || !inPart then return none
            let definition : Block := .footnoteDef (← Lorem.label) #[.text (← sentence)]
            return some (.insertSibling (← beforeOrAfter) (.block definition)),
          -- Insert a sub-part after the last block of a part.
          do
            if !inPart || right.any isBlock then return none
            let part : Part := { title := ← Lorem.title, blocks := #[← newParagraph p params] }
            return some (.insertSibling 1 (.part part))
        ]

/--
An emphasis, bold, link or role with empty content, which can wrap a sequence of inlines, or
{name}`none` when the chosen kind isn't available.
-/
def newWrapper (p : GenreProfile) (defs : Refs) : LoremGen (Option Inline) := do
  match (← Gen.choose Nat 0 4 (by decide)).val with
  | 0 => return some (.emph #[])
  | 1 => return some (.bold #[])
  | 2 => return some (.link #[] (.url s!"https://example.com/{bareWord (← Lorem.word)}"))
  | 3 =>
    if h : defs.links.size = 0 then return none else
    let ⟨k, _, hk⟩ ← Gen.chooseNatLt 0 defs.links.size (by grind)
    return some (.link #[] (.ref defs.links[k]))
  | _ =>
    let roles := p.roles.filter (·.inlineContent)
    if h : roles = [] then return none else
    let spec ← Gen.elements roles (List.length_pos_iff.mpr h)
    return some (.role spec.name (← spec.args) #[])

/-- The edits of a paragraph. -/
def paragraphEdits (p : GenreProfile) (z : Zipper) (content : Array Inline) :
    List (LoremGen (Option Edit)) :=
  let texts := content.zipIdx.filterMap fun (inl, i) =>
    match inl with
    | .text s => some (i, (s.split ' ').length)
    | _ => none
  let defs := z.root.defs
  [ -- Insert text.
    do
      if h : texts.size = 0 then return none else
      let ⟨k, _, hk⟩ ← Gen.chooseNatLt 0 texts.size (by grind)
      let (i, len) := texts[k]
      let at_ := (← Gen.choose Nat 0 len (Nat.zero_le _)).val
      return some (.editText i at_ 0 (← words (← Gen.choose Nat 1 4 (by decide)).val)),
    -- Remove text.
    do
      if h : texts.size = 0 then return none else
      let ⟨k, _, hk⟩ ← Gen.chooseNatLt 0 texts.size (by grind)
      let (i, len) := texts[k]
      let start := (← Gen.choose Nat 0 (len - 1) (Nat.zero_le _)).val
      let longest := Nat.max 1 (Nat.min 3 (len - start))
      let count := (← Gen.choose Nat 1 longest (Nat.le_max_left ..)).val
      return some (.editText i start count ""),
    -- Wrap inlines.
    do
      let some start ← index? content.size | return none
      let latest := Nat.max (start + 1) (Nat.min content.size (start + 2))
      let stop := (← Gen.choose Nat (start + 1) latest (Nat.le_max_left ..)).val
      return (← newWrapper p defs).map (.wrapInlines start stop ·),
    -- Unwrap an inline.
    do return (← index? content.size).map .unwrapInline,
    -- Insert an image, inline code or a footnote use.
    do
      let i := (← Gen.choose Nat 0 content.size (Nat.zero_le _)).val
      let w := bareWord (← Lorem.word) |>.toLower
      let w := if w.isEmpty then "lorem" else w
      let inl ← match (← Gen.choose Nat 0 2 (by decide)).val with
        | 0 => pure (some (Inline.image w s!"https://example.com/{w}.png"))
        | 1 => pure (some (.code w))
        | _ =>
          if h : defs.footnotes.size = 0 then pure none
          else
            let ⟨k, _, hk⟩ ← Gen.chooseNatLt 0 defs.footnotes.size (by grind)
            pure (some (.footnote defs.footnotes[k]))
      return inl.map (.insertInline i ·),
    -- Remove an inline.
    do return (← index? content.size).map .removeInline
  ]

/-- The edits of the focused node's own contents. -/
def focusEdits (p : GenreProfile) (params : Params) (z : Zipper) : List (LoremGen (Option Edit)) :=
  match z.focus with
  | .part part =>
    let fields := part.metadata.toList.map (·.1)
    [ do return some (.setTitle (← Lorem.title)),
      do
        let unset := p.metadata.filter (!fields.contains ·.name)
        if h : unset = [] then return none else
        let f ← Gen.elements unset (List.length_pos_iff.mpr h)
        return some (.addMetadata f.name (← f.value)),
      do
        if h : fields = [] then return none else
        return some (.removeMetadata (← Gen.elements fields (List.length_pos_iff.mpr h))),
      do
        let set := p.metadata.filter (fields.contains ·.name)
        if h : set = [] then return none else
        let f ← Gen.elements set (List.length_pos_iff.mpr h)
        return some (.changeMetadata f.name (← f.value))
    ]
  | .item .. | .descItem .. => []
  | .block b =>
    match b with
    | .ul .. | .ol .. | .dl .. | .blockquote .. => []
    | .directive .. =>
      [ do
          let dirs := usableDirectives p z.inDirective
          if h : dirs = [] then return none else
          let d ← Gen.elements dirs (List.length_pos_iff.mpr h)
          return some (.changeDirective d.name (← d.args))
      ]
    | .para c => paragraphEdits p z c
    | .code name _ lines =>
      match p.codeBlock? name with
      | some spec => (spec.content.edits params lines).map fun g => do return (← g).map .changeLines
      | none => []
    | .command name _ =>
      match p.command? name with
      | some spec => [do return some (.changeCommandArgs (← spec.args))]
      | none => []
    | .linkDef .. =>
      [do return some (.changeLinkDef s!"https://example.com/{bareWord (← Lorem.word)}")]
    | .footnoteDef .. => [do return some (.changeFootnoteDef #[.text (← sentence)])]

/-- The candidate edits at the focus: edits of its own contents and sibling edits. -/
def candidates (p : GenreProfile) (params : Params) (z : Zipper) : List (LoremGen (Option Edit)) :=
  focusEdits p params z ++ siblingEdits p params z

/--
With a chance of {name}`editChance` percent, chooses an edit at the focus. The edit is one of the
candidates for the focused node. It applies, and it changes the concretized text. The first byte
that it changes is at or after {name}`earliestAllowedChange`.
-/
public def pickEdit (p : GenreProfile) (params : Params) (editChance : Nat) (z : Zipper)
    (earliestAllowedChange : String.Pos.Raw := 0) : LoremGen (Option Edit) := do
  unless ← chance editChance do return none
  let before := concretizeDocument p z.root
  for c in (← Gen.permutationOf (candidates p params z)).val do
    if let some e ← c then
      if let some z' := applyEdit p e z then
        let after := concretizeDocument p z'.root
        if after != before && before.firstDiffPos after ≥ earliestAllowedChange then
          return some e
  return none
