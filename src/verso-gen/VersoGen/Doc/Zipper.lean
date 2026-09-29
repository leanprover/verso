/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.Doc.Basic

set_option doc.verso true

/-!
A zipper over surface documents, which the edit pass uses to visit and edit nodes. Besides its
focus, the zipper keeps the context that leads back to the root part, so that an edit at the focus
gives the whole edited document. The zipper's traversal visits nodes in document order, and the
theorems at the end show that its moves leave the root part unchanged.
-/

namespace VersoGen.Doc

open SurfaceDoc

/-- A part with the sub-part on the zipper's path to the focus taken out. -/
public structure PartFrame where
  title : String
  metadata : Array (String × String)
  blocks : Array Block
  /-- The sub-parts before the one taken out. -/
  left : Array Part
  /-- The sub-parts after the one taken out. -/
  right : Array Part
deriving Inhabited

/-- The part, with {name}`p` in the place of the sub-part that was taken out. -/
@[simp] def PartFrame.plug (f : PartFrame) (p : Part) : Part :=
  { f with
    subParts := f.left ++ #[p] ++ f.right }

/--
The context of a list item: whether the list is ordered, the items before and after the item, and
the list's context, of type {name}`α`.
-/
public structure ItemCtx (α : Type) where
  ordered : Bool
  left : Array (Array Block)
  right : Array (Array Block)
  ctx : α
deriving Inhabited

/--
The context of a description list item: the items before and after it and the list's context, of
type {name}`α`.
-/
public structure DescItemCtx (α : Type) where
  left : Array DescItem
  right : Array DescItem
  ctx : α
deriving Inhabited

/--
The context of a block: the blocks before and after it, the node that contains them, and that
node's context.
-/
public inductive BlockCtx where
  /-- In a part's blocks. The frames lead from the part's parent to the root part. -/
  | part (title : String) (metadata : Array (String × String)) (left right : Array Block)
      (subParts : Array Part) (frames : List PartFrame)
  | blockquote (left right : Array Block) (ctx : BlockCtx)
  | directive (name args : String) (left right : Array Block) (ctx : BlockCtx)
  | item (left right : Array Block) (ctx : ItemCtx BlockCtx)
  | descItem (term : Array Inline) (left right : Array Block) (ctx : DescItemCtx BlockCtx)

public instance : Inhabited BlockCtx := ⟨.part "" #[] #[] #[] #[] []⟩

def listBlock (ordered : Bool) (items : Array (Array Block)) : Block :=
  if ordered then .ol items else .ul items

/-- The root part, with {name}`p` in the place that the frames describe. -/
def plugFrames (p : Part) (frames : List PartFrame) : Part := frames.foldl (fun p f => f.plug p) p

mutual
  /-- The root part, with {name}`b` in the place that the context describes. -/
  @[simp] def BlockCtx.plug (b : Block) : BlockCtx → Part
    | .part title metadata left right subParts frames =>
      plugFrames { title, metadata, blocks := left ++ #[b] ++ right, subParts } frames
    | .blockquote left right ctx => BlockCtx.plug (.blockquote (left ++ #[b] ++ right)) ctx
    | .directive name args left right ctx =>
      BlockCtx.plug (.directive name args (left ++ #[b] ++ right)) ctx
    | .item left right ctx => ItemCtx.plug (left ++ #[b] ++ right) ctx
    | .descItem term left right ctx => DescItemCtx.plug (term, left ++ #[b] ++ right) ctx

  /-- The root part, with {name}`i` in the place that the context describes. -/
  @[simp] def ItemCtx.plug (i : Array Block) : ItemCtx BlockCtx → Part
    | .mk ordered left right ctx => BlockCtx.plug (listBlock ordered (left ++ #[i] ++ right)) ctx

  /-- The root part, with {name}`i` in the place that the context describes. -/
  @[simp] def DescItemCtx.plug (i : DescItem) : DescItemCtx BlockCtx → Part
    | .mk left right ctx => BlockCtx.plug (.dl (left ++ #[i] ++ right)) ctx
end

public structure PartZipper where
  focus : Part
  /-- The frames from the part's parent to the root part. -/
  frames : List PartFrame
deriving Inhabited

public structure BlockZipper where
  focus : Block
  ctx : BlockCtx
deriving Inhabited

public structure ItemZipper where
  focus : Array Block
  ctx : ItemCtx BlockCtx
deriving Inhabited

public structure DescItemZipper where
  focus : DescItem
  ctx : DescItemCtx BlockCtx
deriving Inhabited

/-- A surface document with a focused part, block, list item or description list item. -/
public inductive Zipper where
  | part (z : PartZipper)
  | block (z : BlockZipper)
  | item (z : ItemZipper)
  | descItem (z : DescItemZipper)
deriving Inhabited

namespace Zipper

/-- A zipper focused on the root part. -/
public def start (doc : Part) : Zipper := .part ⟨doc, []⟩

/-- The root part, with the focus in its place. -/
public def root : Zipper → Part
  | .part ⟨p, frames⟩ => plugFrames p frames
  | .block ⟨b, ctx⟩ => ctx.plug b
  | .item ⟨i, ctx⟩ => ctx.plug i
  | .descItem ⟨i, ctx⟩ => ctx.plug i

public def focus : Zipper → Node
  | .part z => .part z.focus
  | .block z => .block z.focus
  | .item z => .item z.focus
  | .descItem z => .descItem z.focus

/-- The zipper focused on the first block of {name}`blocks`, with the given context for it. -/
def firstBlock? (blocks : Array Block) (ctx : Array Block → BlockCtx) : Option Zipper :=
  blocks[0]?.map fun b => .block ⟨b, ctx (blocks.extract 1)⟩

/-- Moves to the first node in the focus. -/
def down? : Zipper → Option Zipper
  | .part ⟨p, frames⟩ =>
    match p.blocks[0]? with
    | some b =>
      some (.block ⟨b, .part p.title p.metadata #[] (p.blocks.extract 1) p.subParts frames⟩)
    | none =>
      p.subParts[0]?.map fun s =>
        .part ⟨s, { p with left := #[], right := p.subParts.extract 1 } :: frames⟩
  | .block ⟨b, ctx⟩ =>
    match b with
    | .blockquote bs => firstBlock? bs (.blockquote #[] · ctx)
    | .directive name args bs => firstBlock? bs (.directive name args #[] · ctx)
    | .ul items => items[0]?.map fun i => .item ⟨i, .mk false #[] (items.extract 1) ctx⟩
    | .ol items => items[0]?.map fun i => .item ⟨i, .mk true #[] (items.extract 1) ctx⟩
    | .dl items => items[0]?.map fun i => .descItem ⟨i, .mk #[] (items.extract 1) ctx⟩
    | _ => none
  | .item ⟨i, ctx⟩ => firstBlock? i (.item #[] · ctx)
  | .descItem ⟨(term, bs), ctx⟩ => firstBlock? bs (.descItem term #[] · ctx)

/-- Moves from a part to the first following sibling of it or of one of the parts it is in. -/
def skipPart? (p : Part) : List PartFrame → Option Zipper
  | [] => none
  | f :: frames =>
    match f.right[0]? with
    | some r =>
      some (.part ⟨r, { f with left := f.left.push p, right := f.right.extract 1 } :: frames⟩)
    | none => skipPart? (f.plug p) frames

mutual
  /-- Moves from a block to the first following sibling of it or of one of the nodes it is in. -/
  def skipBlock? (b : Block) : BlockCtx → Option Zipper
    | .part title metadata left right subParts frames =>
      match right[0]? with
      | some r =>
        some (.block ⟨r, .part title metadata (left.push b) (right.extract 1) subParts frames⟩)
      | none =>
        let blocks := left.push b
        match subParts[0]? with
        | some s =>
          let frame : PartFrame :=
            { title, metadata, blocks, left := #[], right := subParts.extract 1 }
          some (.part ⟨s, frame :: frames⟩)
        | none => skipPart? { title, metadata, blocks, subParts } frames
    | .blockquote left right ctx =>
      match right[0]? with
      | some r => some (.block ⟨r, .blockquote (left.push b) (right.extract 1) ctx⟩)
      | none => skipBlock? (.blockquote (left.push b)) ctx
    | .directive name args left right ctx =>
      match right[0]? with
      | some r => some (.block ⟨r, .directive name args (left.push b) (right.extract 1) ctx⟩)
      | none => skipBlock? (.directive name args (left.push b)) ctx
    | .item left right ctx =>
      match right[0]? with
      | some r => some (.block ⟨r, .item (left.push b) (right.extract 1) ctx⟩)
      | none => skipItem? (left.push b) ctx
    | .descItem term left right ctx =>
      match right[0]? with
      | some r => some (.block ⟨r, .descItem term (left.push b) (right.extract 1) ctx⟩)
      | none => skipDescItem? (term, left.push b) ctx

  /--
  Moves from a list item to the first following sibling of it or of one of the nodes it is in.
  -/
  def skipItem? (i : Array Block) : ItemCtx BlockCtx → Option Zipper
    | .mk ordered left right ctx =>
      match right[0]? with
      | some r => some (.item ⟨r, .mk ordered (left.push i) (right.extract 1) ctx⟩)
      | none => skipBlock? (listBlock ordered (left.push i)) ctx

  /--
  Moves from a description list item to the first following sibling of it or of one of the nodes it
  is in.
  -/
  def skipDescItem? (i : DescItem) : DescItemCtx BlockCtx → Option Zipper
    | .mk left right ctx =>
      match right[0]? with
      | some r => some (.descItem ⟨r, .mk (left.push i) (right.extract 1) ctx⟩)
      | none => skipBlock? (.dl (left.push i)) ctx
end

/-- Moves to the first following sibling of the focus or of one of the nodes it is in. -/
def skip? : Zipper → Option Zipper
  | .part ⟨p, frames⟩ => skipPart? p frames
  | .block ⟨b, ctx⟩ => skipBlock? b ctx
  | .item ⟨i, ctx⟩ => skipItem? i ctx
  | .descItem ⟨i, ctx⟩ => skipDescItem? i ctx

/-- Moves to the next node in document order. -/
public def next? (z : Zipper) : Option Zipper := z.down? <|> z.skip?

/-- Moves {lit}`n` nodes forward in document order. -/
@[expose] public def nextN : Nat → Zipper → Option Zipper
  | 0, z => some z
  | n + 1, z => (nextN n z).bind next?

/-- The number of nodes directly in the focus. -/
def childCount : Zipper → Nat
  | .part ⟨p, _⟩ => p.blocks.size + p.subParts.size
  | .block ⟨b, _⟩ =>
    match b with
    | .ul items | .ol items => items.size
    | .dl items => items.size
    | .blockquote bs | .directive _ _ bs => bs.size
    | _ => 0
  | .item ⟨i, _⟩ => i.size
  | .descItem ⟨(_, bs), _⟩ => bs.size

/-- The zipper focused on {name}`xs`'s element at {name}`i`, with the context made from the rest. -/
def atIndex? (xs : Array α) (i : Nat) (zip : α → Array α → Array α → Zipper) : Option Zipper :=
  xs[i]?.map fun x => zip x (xs.extract 0 i) (xs.extract (i + 1))

/--
Moves to the node at index {name}`i` of the nodes directly in the focus. A part's blocks come before
its sub-parts.
-/
public def child? (z : Zipper) (i : Nat) : Option Zipper :=
  match z with
  | .part ⟨p, frames⟩ =>
    if i < p.blocks.size then
      atIndex? p.blocks i fun b l r => .block ⟨b, .part p.title p.metadata l r p.subParts frames⟩
    else
      atIndex? p.subParts (i - p.blocks.size) fun s l r =>
        .part ⟨s, { p with left := l, right := r } :: frames⟩
  | .block ⟨b, ctx⟩ =>
    match b with
    | .blockquote bs => atIndex? bs i fun b l r => .block ⟨b, .blockquote l r ctx⟩
    | .directive name args bs => atIndex? bs i fun b l r => .block ⟨b, .directive name args l r ctx⟩
    | .ul items => atIndex? items i fun x l r => .item ⟨x, .mk false l r ctx⟩
    | .ol items => atIndex? items i fun x l r => .item ⟨x, .mk true l r ctx⟩
    | .dl items => atIndex? items i fun x l r => .descItem ⟨x, .mk l r ctx⟩
    | _ => none
  | .item ⟨bs, ctx⟩ => atIndex? bs i fun b l r => .block ⟨b, .item l r ctx⟩
  | .descItem ⟨(term, bs), ctx⟩ => atIndex? bs i fun b l r => .block ⟨b, .descItem term l r ctx⟩

/-- Moves to the focus's parent, the node that contains the focus. -/
public def up? : Zipper → Option Zipper
  | .part ⟨_, []⟩ => none
  | .part ⟨p, f :: frames⟩ => some (.part ⟨f.plug p, frames⟩)
  | .block ⟨b, ctx⟩ =>
    match ctx with
    | .part title metadata left right subParts frames =>
      some (.part ⟨{ title, metadata, blocks := left ++ #[b] ++ right, subParts }, frames⟩)
    | .blockquote left right ctx => some (.block ⟨.blockquote (left ++ #[b] ++ right), ctx⟩)
    | .directive name args left right ctx =>
      some (.block ⟨.directive name args (left ++ #[b] ++ right), ctx⟩)
    | .item left right ctx => some (.item ⟨left ++ #[b] ++ right, ctx⟩)
    | .descItem term left right ctx => some (.descItem ⟨(term, left ++ #[b] ++ right), ctx⟩)
  | .item ⟨i, .mk ordered left right ctx⟩ =>
    some (.block ⟨listBlock ordered (left ++ #[i] ++ right), ctx⟩)
  | .descItem ⟨i, .mk left right ctx⟩ => some (.block ⟨.dl (left ++ #[i] ++ right), ctx⟩)

/-- The index of the focus among the children of its parent. -/
public def indexInParent : Zipper → Nat
  | .part ⟨_, []⟩ => 0
  | .part ⟨_, f :: _⟩ => f.blocks.size + f.left.size
  | .block ⟨_, ctx⟩ =>
    match ctx with
    | .part _ _ left .. | .blockquote left .. | .directive _ _ left .. | .item left ..
    | .descItem _ left .. => left.size
  | .item ⟨_, .mk _ left ..⟩ => left.size
  | .descItem ⟨_, .mk left ..⟩ => left.size

public def lastChild? (z : Zipper) : Option Zipper :=
  if z.childCount == 0 then none else z.child? (z.childCount - 1)

/--
Moves to the last node in the focus in document order, or stays at a focus without children.
-/
public partial def lastDescendant (z : Zipper) : Zipper :=
  match z.lastChild? with
  | some z' => lastDescendant z'
  | none => z

/-- Moves to the focus's previous sibling. -/
def left? (z : Zipper) : Option Zipper := do
  let i := z.indexInParent
  if i == 0 then none else (← z.up?).child? (i - 1)

/--
Moves to the node before the focus in document order, from which {name}`next?` returns to the focus.
-/
public def prev? (z : Zipper) : Option Zipper :=
  match z.left? with
  | some z' => some z'.lastDescendant
  | none => z.up?

/-- The indices of the nodes that lead from the root part to the focus. -/
public partial def indexPath (z : Zipper) : List Nat :=
  match z.up? with
  | some parent => parent.indexPath ++ [z.indexInParent]
  | none => []

/-- Moves to the node at a path of indices from the root part. -/
public def goto (doc : Part) (path : List Nat) : Option Zipper :=
  path.foldlM child? (start doc)

/--
The zipper with its focus replaced by a node of the same kind, or {name}`none` for another kind.
-/
public def replaceFocus? (z : Zipper) (n : Node) : Option Zipper :=
  match z, n with
  | .part z, .part p => some (.part { z with focus := p })
  | .block z, .block b => some (.block { z with focus := b })
  | .item z, .item i => some (.item { z with focus := i })
  | .descItem z, .descItem i => some (.descItem { z with focus := i })
  | _, _ => none

public partial def inDirective (z : Zipper) : Bool :=
  match z.up? with
  | some parent => parent.focus matches .block (.directive ..) || parent.inDirective
  | none => false

/-!
# The Traversal Keeps the Document

These theorems check a basic property of the zipper: traversing a document with the zipper doesn't
change its contents.
-/

/-- Arrays with a first element are that element followed by the elements after it. -/
private theorem array_singleton_append_extract_one {xs : Array α} {x : α} (h : xs[0]? = some x) :
    #[x] ++ xs.extract 1 = xs := by
  ext <;> grind

/-- Pushing an array's first element and then appending the elements after it appends the array. -/
private theorem array_push_append_extract_one {xs ys : Array α} {y : α} (h : ys[0]? = some y) :
    xs.push y ++ ys.extract 1 = xs ++ ys := by
  rw [← Array.append_singleton, Array.append_assoc, array_singleton_append_extract_one h]

/-- Appending an element and an array without a first element pushes the element. -/
private theorem array_append_singleton_append_of_getElem?_zero_eq_none {xs ys : Array α} {y : α}
    (h : ys[0]? = none) : xs ++ #[y] ++ ys = xs.push y := by
  grind

/-- Plugging a part into an empty list of frames gives the part. -/
@[simp] theorem plugFrames_nil {p : Part} : plugFrames p [] = p := rfl

/-- Plugging a part into frames plugs it into the innermost frame first. -/
@[simp] theorem plugFrames_cons {p : Part} {f : PartFrame} {frames : List PartFrame} :
    plugFrames p (f :: frames) = plugFrames (f.plug p) frames := rfl

/-- Unordered list blocks are bulleted lists. -/
@[simp] theorem listBlock_false {items : Array (Array Block)} : listBlock false items = .ul items :=
  rfl

/-- Ordered list blocks are numbered lists. -/
@[simp] theorem listBlock_true {items : Array (Array Block)} : listBlock true items = .ol items :=
  rfl

/-- The root part of a zipper focused on a part is the part plugged into its frames. -/
@[simp] theorem root_part {p : Part} {frames : List PartFrame} :
    (Zipper.part ⟨p, frames⟩).root = plugFrames p frames := rfl

/-- The root part of a zipper focused on a block is the block plugged into its context. -/
@[simp] theorem root_block {b : Block} {ctx : BlockCtx} :
    (Zipper.block ⟨b, ctx⟩).root = ctx.plug b := rfl

/-- The root part of a zipper focused on a list item is the item plugged into its context. -/
@[simp] theorem root_item {i : Array Block} {ctx : ItemCtx BlockCtx} :
    (Zipper.item ⟨i, ctx⟩).root = ctx.plug i := rfl

/--
The root part of a zipper focused on a description list item is the item plugged into its context.
-/
@[simp] theorem root_descItem {i : DescItem} {ctx : DescItemCtx BlockCtx} :
    (Zipper.descItem ⟨i, ctx⟩).root = ctx.plug i := rfl

/-- Moving to the first node in the focus keeps the document. -/
theorem root_eq_of_down?_eq_some {z z' : Zipper} (h : z.down? = some z') : z'.root = z.root := by
  match z with
  | .part ⟨⟨title, metadata, blocks, subParts⟩, frames⟩ =>
    rw [down?] at h
    split at h
    · next b hb =>
      cases h
      simp [array_singleton_append_extract_one hb]
    · next hb =>
      obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [array_singleton_append_extract_one hs]
  | .block ⟨b, ctx⟩ =>
    cases b <;> simp only [down?, firstBlock?, Option.map_eq_some_iff, reduceCtorEq] at h <;>
      obtain ⟨x, hx, rfl⟩ := h <;> simp [array_singleton_append_extract_one hx]
  | .item ⟨i, ctx⟩ | .descItem ⟨(_, i), ctx⟩ =>
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [array_singleton_append_extract_one hx]

/-- Moving from a part to the next sibling of it or of a part it is in keeps the document. -/
theorem root_eq_of_skipPart?_eq_some {p : Part} {frames : List PartFrame} {z : Zipper}
    (h : skipPart? p frames = some z) : z.root = plugFrames p frames := by
  fun_induction skipPart? p frames with
  | case1 => simp at h
  | case2 p f frames r hr =>
    cases h
    simp [array_push_append_extract_one hr]
  | case3 p f frames hr ih => rw [plugFrames_cons]; exact ih h

/--
Moving from a block in a part's blocks to the next sibling of it or of a part it is in keeps the
document.
-/
theorem root_eq_of_skipBlock?_part_eq_some {b : Block} {title : String}
    {metadata : Array (String × String)} {left right : Array Block} {subParts : Array Part}
    {frames : List PartFrame} {z : Zipper}
    (h : skipBlock? b (.part title metadata left right subParts frames) = some z) :
    z.root = (BlockCtx.part title metadata left right subParts frames).plug b := by
  rw [skipBlock?] at h
  split at h
  · next hr => cases h; simp [array_push_append_extract_one hr]
  · next hr =>
    rw [BlockCtx.plug, array_append_singleton_append_of_getElem?_zero_eq_none hr]
    split at h
    · next hs => cases h; simp [array_singleton_append_extract_one hs]
    · next hs => exact root_eq_of_skipPart?_eq_some h

mutual
  /-- Moving from a block to the next sibling of it or of a node it is in keeps the document. -/
  theorem root_eq_of_skipBlock?_eq_some {z : Zipper} :
      (ctx : BlockCtx) → (b : Block) → skipBlock? b ctx = some z → z.root = ctx.plug b
    | .part .., _, h => root_eq_of_skipBlock?_part_eq_some h
    | .blockquote _ _ ctx, b, h | .directive _ _ _ _ ctx, b, h => by
      rw [skipBlock?] at h
      split at h
      · next hr => cases h; simp [array_push_append_extract_one hr]
      · next hr =>
        rw [root_eq_of_skipBlock?_eq_some ctx _ h, BlockCtx.plug,
          array_append_singleton_append_of_getElem?_zero_eq_none hr]
    | .item _ _ ctx, b, h => by
      rw [skipBlock?] at h
      split at h
      · next hr => cases h; simp [array_push_append_extract_one hr]
      · next hr =>
        rw [root_eq_of_skipItem?_eq_some ctx _ h, BlockCtx.plug,
          array_append_singleton_append_of_getElem?_zero_eq_none hr]
    | .descItem _ _ _ ctx, b, h => by
      rw [skipBlock?] at h
      split at h
      · next hr => cases h; simp [array_push_append_extract_one hr]
      · next hr =>
        rw [root_eq_of_skipDescItem?_eq_some ctx _ h, BlockCtx.plug,
          array_append_singleton_append_of_getElem?_zero_eq_none hr]

  /-- Moving from a list item to the next sibling of it or of a node it is in keeps the document. -/
  theorem root_eq_of_skipItem?_eq_some {z : Zipper} :
      (ctx : ItemCtx BlockCtx) → (i : Array Block) → skipItem? i ctx = some z →
        z.root = ctx.plug i
    | .mk _ _ _ ctx, i, h => by
      rw [skipItem?] at h
      split at h
      · next hr => cases h; simp [array_push_append_extract_one hr]
      · next hr =>
        rw [root_eq_of_skipBlock?_eq_some ctx _ h, ItemCtx.plug,
          array_append_singleton_append_of_getElem?_zero_eq_none hr]

  /--
  Moving from a description list item to the next sibling of it or of a node it is in keeps the
  document.
  -/
  theorem root_eq_of_skipDescItem?_eq_some {z : Zipper} :
      (ctx : DescItemCtx BlockCtx) → (i : DescItem) →
        skipDescItem? i ctx = some z → z.root = ctx.plug i
    | .mk _ _ ctx, i, h => by
      rw [skipDescItem?] at h
      split at h
      · next hr => cases h; simp [array_push_append_extract_one hr]
      · next hr =>
        rw [root_eq_of_skipBlock?_eq_some ctx _ h, DescItemCtx.plug,
          array_append_singleton_append_of_getElem?_zero_eq_none hr]
end

/-- Moving to the next sibling of the focus or of a node it is in keeps the document. -/
theorem root_eq_of_skip?_eq_some {z z' : Zipper} (h : z.skip? = some z') : z'.root = z.root := by
  match z with
  | .part ⟨p, frames⟩ => exact root_eq_of_skipPart?_eq_some h
  | .block ⟨b, ctx⟩ => exact root_eq_of_skipBlock?_eq_some ctx b h
  | .item ⟨i, ctx⟩ => exact root_eq_of_skipItem?_eq_some ctx i h
  | .descItem ⟨i, ctx⟩ => exact root_eq_of_skipDescItem?_eq_some ctx i h

/-- Moving to the next node in document order keeps the document. -/
theorem root_eq_of_next?_eq_some {z z' : Zipper} (h : z.next? = some z') : z'.root = z.root := by
  cases hdown : z.down? with
  | none => exact root_eq_of_skip?_eq_some (by simpa [next?, hdown] using h)
  | some d =>
    have hd : d = z' := by simpa [next?, hdown] using h
    exact hd ▸ root_eq_of_down?_eq_some hdown

/-- Moving {lit}`n + 1` nodes forward moves {lit}`n` nodes forward and then to the next node. -/
public theorem nextN_succ {n : Nat} {z : Zipper} : nextN (n + 1) z = (nextN n z).bind next? :=
  rfl

/-- Moving forward in document order keeps the document. -/
public theorem root_eq_of_nextN_eq_some {n : Nat} {z z' : Zipper} (h : nextN n z = some z') :
    z'.root = z.root := by
  fun_induction nextN n z generalizing z' with
  | case1 z => cases h; rfl
  | case2 n z ih =>
    obtain ⟨z'', hsteps, hnext⟩ := Option.bind_eq_some_iff.1 h
    rw [root_eq_of_next?_eq_some hnext, ih hsteps]
