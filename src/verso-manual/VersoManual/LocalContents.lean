/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso
import MultiVerso.Slug
import VersoManual.Basic


open Lean
open Verso.Multi

namespace Verso.Genre.Manual

open Doc

abbrev LocalContentItemRecognizer :=
  Manual.Block → Option (Array (Doc.Inline Manual) × Slug)

def LocalContentItemRecognizer.failure : LocalContentItemRecognizer := fun _ => Option.none

def LocalContentItemRecognizer.orElse (r1 r2 : LocalContentItemRecognizer) : LocalContentItemRecognizer := fun b => r1 b <|> r2 b

initialize localContentAttr : TagAttribute ←
  registerTagAttribute `local_content_list "Functions that recognize items for the page-local table of contents"

private def localContentRecognizers [Monad m] [MonadLiftT MetaM m] [MonadOptions m] [MonadEnv m] [MonadError m] : m (Array Name) := do
  let st := localContentAttr.ext.toEnvExtension.getState (← getEnv)
  let st' := st.importedEntries.flatten ++ st.state.toArray

  let mut out := #[]
  for f in st' do
    let t ← Meta.inferType (.const f [])
    if (← Meta.isDefEq t (.const ``LocalContentItemRecognizer [])) then
      out := out.push f
    else
      throwError m!"Recognizer '{f}' has type '{t}' (expected {``LocalContentItemRecognizer}')"
  pure out

open Lean Elab Term in
scoped elab "local_content_recognizer_fun" : term => do
  let mut stx ← ``(LocalContentItemRecognizer.failure)
  let rs ← localContentRecognizers
  for f in rs do
    stx ← `($(mkIdent f) <|> $stx)
  elabTerm stx none

structure HeaderStatus where
  level : Nat
  numbering : Option String
deriving Repr

open Verso.Output in
structure LocalContentItem where
  header? : Option HeaderStatus
  dest : String
  linkTexts : Array (String × Html)
  linkTexts_nonempty : linkTexts.size > 0
deriving Repr

partial def fromNone : Doc.Inline Genre.none → Doc.Inline Manual
  | .text s => .text s
  | .concat xs => .concat (xs.map fromNone)
  | .image alt dest => .image alt dest
  | .link xs dest => .link (xs.map fromNone) dest
  | .linebreak s => .linebreak s
  | .code s => .code s
  | .emph xs => .emph (xs.map fromNone)
  | .bold xs => .bold (xs.map fromNone)
  | .math mode x => .math mode x
  | .footnote x xs => .footnote x (xs.map fromNone)

partial def toNone : Doc.Inline Manual → Doc.Inline Genre.none
  | .other _ is => .concat (is.map toNone)
  | .text s => .text s
  | .concat xs => .concat (xs.map toNone)
  | .image alt dest => .image alt dest
  | .link xs dest => .link (xs.map toNone) dest
  | .linebreak s => .linebreak s
  | .code s => .code s
  | .emph xs => .emph (xs.map toNone)
  | .bold xs => .bold (xs.map toNone)
  | .math mode x => .math mode x
  | .footnote x xs => .footnote x (xs.map toNone)

open Verso.Output Html

def LocalContentItem.toHtml (item : LocalContentItem) : Html :=
  have := item.linkTexts_nonempty
  let txt := {{<a href={{item.dest}}>{{item.linkTexts[0].2}}</a>}}
  if let some ⟨level, numbering⟩ := item.header? then
    let numHtml := if let some l := numbering then {{<span class="level-num">{{l}}</span>" "}} else .empty
    {{<span class=s!"header head-{level}">{{numHtml}}{{txt}}</span>}}
  else
    txt

section GetItems

structure LocalItemState where
  errors : Array String
  items : Array LocalContentItem

def LocalItemState.save (item : LocalContentItem) (st : LocalItemState) : LocalItemState :=
  {st with items := st.items.push item}

def LocalItemState.logError (error : String) (st : LocalItemState) : LocalItemState :=
  {st with errors := st.errors.push error}

variable [Monad m] [MonadState LocalItemState m]
variable (impls : ExtensionImpls) (xref : TraverseState)

partial def inlineItem (inl : Inline) (contents : Array (Doc.Inline Manual)) : m Unit := do
  if let some impl := impls.getInline? inl.name then
    if let some id := inl.id then
    match impl.localContentItem id inl.data contents with
    | .error e => modify (·.logError s!"Error generating local ToC item for '{inl.name}': {e}")
    | .ok names =>
      if h : names.size > 0 then
        if let some dest := xref.externalTags[id]? then
          modify (·.save ⟨none, dest.link, names, h⟩)

partial def inlineContents (i : Doc.Inline Manual) : m Unit := do
  match i with
  | .concat xs | .footnote _ xs | .link xs _ | .bold xs | .emph xs =>
    xs.forM inlineContents
  | .other inl is =>
    inlineItem impls xref inl is
    is.forM inlineContents
  | .image .. | .linebreak .. | .math .. | .code .. | .text ..=> pure ()

partial def blockItem (blk : Block) (contents : Array (Doc.Block Manual)) : m Unit := do
  if let some impl := impls.getBlock? blk.name then
    if let some id := blk.id then
      match impl.localContentItem id blk.data contents with
      | .error e => modify (·.logError s!"Error generating local ToC item for '{blk.name}': {e}")
      | .ok names =>
        if h : names.size > 0 then
          if let some dest := xref.externalTags[id]? then
            modify (·.save ⟨none, dest.link, names, h⟩)

partial def blockContents (b : Doc.Block Manual) : m Unit := do
  match b with
  | .para txt =>
    txt.forM (inlineContents impls xref)
  | .code .. => pure ()
  | .concat xs | .blockquote xs =>
    xs.forM blockContents
  | .ul xs | .ol _ xs =>
    xs.forM (·.contents.forM blockContents)
  | .dl xs =>
    for x in xs do
      for i in x.term do
        inlineContents impls xref i
      for y in x.desc do
        blockContents  y
  | .other blk bs =>
    blockItem impls xref blk bs
    bs.forM blockContents

end GetItems

def uniquifyLocalItems (items : Array LocalContentItem) : Array LocalContentItem := Id.run do
  let mut items := items
  for j in [0:15] do -- Upper bound on rounds - more than 3 is unlikely, so this should just save us from malicious code
    let ambiguous :=
      items
        |>.groupByKey (fun x => have := x.linkTexts_nonempty; x.linkTexts[0].1)
        |>.filter (fun _ arr => arr.size > 1)
        |>.keys
        |> Std.HashSet.ofList
    if ambiguous.isEmpty then break
    let mut items' := #[]
    let mut changed := false
    for i in items do
      have := i.linkTexts_nonempty
      if i.linkTexts[0].1 ∈ ambiguous then
        -- Attempt to take the next preference
        if h : i.linkTexts.size > 1 then
          items' := items'.push { i with
            linkTexts := i.linkTexts.drop 1,
            linkTexts_nonempty := by simp; omega
          }
          changed := true
          continue
      items' := items'.push i
    if changed then items := items' else break
  return items


/--
How far down the tree should be traversed when collecting local items?
-/
inductive SubpartSpec where
  /-- Include only the part itself, as a header. -/
  | none
  /-- Include `n` levels of content below the current header. -/
  | depth (n : Nat) : SubpartSpec
  /-- Include all levels of content below the current header. -/
  | all
deriving DecidableEq, Repr

instance : Ord SubpartSpec where
  compare
    | .none, .none => .eq
    | .none, _ => .lt
    | .depth _, .none => .gt
    | .depth n, .depth n' => compare n n'
    | .depth _, .all => .lt
    | .all, .all => .eq
    | .all, _ => .gt

def SubpartSpec.isNone : SubpartSpec → Bool
  | .none => true
  | _ => false

def SubpartSpec.decr : SubpartSpec → SubpartSpec
  | .none => .none
  | .depth 0 => .none
  | .depth (n + 1) => .depth n
  | .all => .all

instance : LT SubpartSpec := Ord.toLT inferInstance
instance : LE SubpartSpec := Ord.toLE inferInstance

partial def localContentsCore
    (opts : Html.Options (ReaderT ExtensionImpls IO)) (ctxt : TraverseContext) (xref : TraverseState)
    (p : Part Manual) (sectionNumPrefix : Option String)
    (includeTitle : Bool) (includeSubparts : SubpartSpec) (fromLevel : Nat) :
    StateT LocalItemState (StateT (Code.Hover.State Html) (ReaderT ExtensionImpls IO)) Unit := do
  let sectionNumPrefix := sectionNumPrefix <|> sectionString ctxt

  if includeTitle then
    let shortTitle := p.metadata.bind (·.shortTitle)
    let titleHtml ←
      if let some title := shortTitle then
        pure (Html.ofString title)
      else
        let (html, _) ← p.title.mapM (Manual.toHtml opts ctxt xref {} {} {} ·) |>.run {}
        pure html

    let partDest : Option LocalContentItem := do
      let m ← p.metadata
      let id ← m.id
      let dest ← xref.externalTags[id]?
      let num := sectionString ctxt |>.map (withoutPrefix · sectionNumPrefix)

      return ⟨some ⟨fromLevel, num⟩, dest.link, #[(shortTitle.getD p.titleString, titleHtml)], by simp⟩
    if let some here := partDest then modify (·.save here)

  if includeSubparts > .none then
    for b in p.content do
      blockContents (← readThe ExtensionImpls) xref b
    for p' in p.subParts do
      -- In the recursive cases, `includeTitle` is `true` because all the sections and subsections
      -- on the page should be listed in the local ToC
      localContentsCore opts (ctxt.inPart p') xref p' sectionNumPrefix true includeSubparts.decr (fromLevel + 1)
where
  withoutPrefix (str : String) (prefix? : Option String) : String :=
    prefix?.bind (str.dropPrefix? · |>.map String.Slice.copy) |>.getD str

def localContents
    (opts : Html.Options (ReaderT ExtensionImpls IO)) (ctxt : TraverseContext) (xref : TraverseState)
    (p : Part Manual)
    (sectionNumPrefix : Option String := none)
    (includeTitle : Bool := true) (includeSubparts : SubpartSpec := .all) (fromLevel : Nat := 0) :
    StateT (Code.Hover.State Html) (ReaderT ExtensionImpls IO) (Array String × Array LocalContentItem) := do
  let ((), ⟨errs, items⟩) ←
    StateT.run
      (localContentsCore opts ctxt xref p
        (sectionNumPrefix := sectionNumPrefix)
        (includeTitle := includeTitle)
        (includeSubparts := includeSubparts)
        (fromLevel := fromLevel))
      ⟨#[], #[]⟩
  return (errs, uniquifyLocalItems items)
