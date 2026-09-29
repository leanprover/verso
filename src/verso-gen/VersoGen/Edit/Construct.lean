/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.Edit.Pass

set_option doc.verso true

/-!
Generation of documents by construction: the edit pass, run from the empty document, inserts every
node of a new document. Each edit inserts nodes that are empty at first, and the pass reaches them
in document order and fills each one in turn, so the document is valid when construction ends.
Replaying the recorded edits from the empty document gives the document again.
-/

namespace VersoGen.Edit

open VersoGen.Doc VersoGen.Doc.SurfaceDoc VersoGen.Genre VersoGen.Random VersoGen.Text Plausible

/-- The empty document: a part without a title, metadata, blocks or sub-parts. -/
public def emptyDocument : Part := { title := "" }

/-- The numbers of top-level blocks and of parts that construction may still add. -/
structure Budget where
  blocks : Nat
  parts : Nat

structure ConstructState where
  budget : Budget
  /--
  The generated nodes whose contents are still to be inserted, in the order that the pass reaches
  them, the next one last.
  -/
  pending : Array Node := #[]
  /-- The definitions for the link and footnote uses of pending paragraphs. -/
  definitions : Array Block := #[]
  /-- The edits still to make at the focus, the next one last. -/
  edits : Array Edit := #[]
  /-- Whether construction has chosen its edits at the focus. -/
  atFocus : Bool := false

abbrev ConstructM := StateT ConstructState LoremGen

/--
The node as construction inserts it: a container without its children or a paragraph without its
link and footnote uses.
-/
def emptied : Node → Node
  | .block (.para c) => .block (.para (c.filter (!isUse ·)))
  | .block (.ul _) => .block (.ul #[])
  | .block (.ol _) => .block (.ol #[])
  | .block (.dl _) => .block (.dl #[])
  | .block (.blockquote _) => .block (.blockquote #[])
  | .block (.directive name args _) => .block (.directive name args #[])
  | .item _ => .item #[]
  | .descItem (term, _) => .descItem (term, #[])
  | n => n
where
  /-- Whether an inline is a link or footnote use. -/
  isUse : Inline → Bool
    | .link _ (.ref _) | .footnote _ => true
    | _ => false

/-- The label of a link or footnote use. -/
def useLabel? : Inline → Option String
  | .link _ (.ref label) | .footnote label => some label
  | _ => none

/-- The label of a link or footnote definition. -/
def definitionLabel? : Block → Option String
  | .linkDef label _ | .footnoteDef label _ => some label
  | _ => none

/--
The edits that insert nodes into the focus from index {name}`offset`, each emptied. The nodes are
recorded as pending, so that the pass fills them when it reaches them.
-/
def insertChildren (offset : Nat) (children : Array Node) : ConstructM (Array Edit) := do
  modify fun st => { st with pending := st.pending ++ children.reverse }
  return children.mapIdx fun i n => .contents (.insert (offset + i) (emptied n))

/--
The edits at a new part at depth {name}`depth`: its title and metadata, its empty sub-parts, and
its top-level blocks. The part's top-level blocks spend the budget of blocks until it is spent or
the part starts sub-parts, and its sub-parts spend some of the budget of parts.
-/
def newPartEdits (p : GenreProfile) (params : Params) (depth : Nat) : ConstructM (Array Edit) := do
  let mayNest := depth < params.partDepth
  let title ← Lorem.title
  let metadata ← if (← chance params.metadataChance) then genMetadata p else pure #[]
  let mut blocks : Array Node := #[]
  let mut afterDescriptionList := false
  repeat
    let budget := (← get).budget
    if budget.blocks == 0 then break
    if budget.parts > 0 && mayNest then
      if ← chance (100 * budget.parts / (budget.parts + budget.blocks)) then break
    let g ← genBlock p params 0 0 BlockKind.exceptDefinitions
      (afterDescriptionList := afterDescriptionList)
    blocks := blocks.push (.block g.block)
    afterDescriptionList := g.block matches .dl ..
    modify fun st =>
      { st with budget.blocks := st.budget.blocks - 1, definitions := st.definitions ++ g.defs }
  let parts := (← get).budget.parts
  let subParts ←
    if h : 0 < parts ∧ mayNest then pure (← Gen.choose Nat 1 parts h.1).val else pure 0
  modify fun st => { st with budget.parts := st.budget.parts - subParts }
  let partEdits := #[Edit.setTitle title] ++ metadata.map (fun (f, v) => Edit.addMetadata f v) ++
    (if subParts > 0 then #[Edit.addSubParts subParts] else #[])
  return partEdits ++ (← insertChildren 0 blocks)

/--
The edits at a paragraph whose generated contents are {name}`content`: each link or footnote use
with its definition, in the order of the uses. Uses are left out if the document already has a
definition with their label.
-/
def referenceEdits (doc : Part) (content : Array Inline) : ConstructM (Array Edit) := do
  let defined := doc.defs
  let mut out := #[]
  let mut index := 0
  for inl in content do
    match useLabel? inl with
    | none => index := index + 1
    | some label =>
      let some definition := (← get).definitions.find? (definitionLabel? · == some label)
        | continue
      if defined.links.contains label || defined.footnotes.contains label then continue
      let place ← Gen.elements [.beforeBlock, .afterBlock, .documentEnd] (by decide)
      out := out.push (.reference { index, use := inl, definition, place })
      index := index + 1
  return out

/-- The edits that construction makes at the focus. -/
def constructionEdits (p : GenreProfile) (params : Params) (z : Zipper) :
    ConstructM (Array Edit) := do
  match z with
  | .part ⟨part, frames⟩ =>
    if part.title.isEmpty then newPartEdits p params frames.length else return #[]
  | _ =>
    if z.focus matches .block (.linkDef ..) | .block (.footnoteDef ..) then return #[]
    let st ← get
    let some full := st.pending.back? | return #[]
    set { st with pending := st.pending.pop }
    match full with
    | .block (.para content) => referenceEdits z.root content
    | .block (.ul items) | .block (.ol items) => insertChildren 0 (items.map .item)
    | .block (.dl items) => insertChildren 0 (items.map .descItem)
    | .block (.blockquote bs) | .block (.directive _ _ bs) | .item bs | .descItem (_, bs) =>
      insertChildren 0 (bs.map .block)
    | _ => return #[]

/--
The choice that construction makes at a focus. At a focus that it has not reached before, it
chooses all of its edits there. It then makes them one at a time. With no edits left, it moves on.
-/
def constructionChoice (p : GenreProfile) (params : Params) (z : Zipper)
    (_ : String.Pos.Raw) (s : ConstructState × LoremState × StdGen) :
    Option Edit × ConstructState × LoremState × StdGen :=
  let (st, gen) := s
  if let some e := st.edits.back? then (some e, { st with edits := st.edits.pop }, gen)
  else if st.atFocus then (none, { st with atFocus := false }, gen)
  else
    match ((constructionEdits p params z).run st).runFrom gen with
    | .ok ((edits, st), gen) =>
      let edits := edits.reverse
      match edits.back? with
      | some e => (some e, { st with edits := edits.pop, atFocus := true }, gen)
      | none => (none, st, gen)
    | .error _ => (none, st, gen)

/-- The largest number of node visits of a construction with some parameters. -/
def constructionLimit (params : Params) : Nat := 1000 * (params.topLevelBlocks + params.parts + 1)

/-- Generates a document and the recorded edits that construct it from the empty document. -/
public def constructDocument (p : GenreProfile) (params : Params) :
    LoremGen (Part × List RecordedEdit) :=
  LoremGen.ofStateFn fun (lorem, rng) =>
    let budget := { blocks := params.topLevelBlocks, parts := params.parts }
    let st : ConstructState := { budget }
    let ((z, es), (_, gen)) := editPassWith p (constructionChoice p params)
      (constructionLimit params) (.start emptyDocument) 0 0 (st, lorem, rng)
    ((z.root, es), gen)

public def genDocument (p : GenreProfile) (params : Params) : LoremGen Part :=
  (·.1) <$> constructDocument p params
