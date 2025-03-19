/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso
import VersoManual.Basic

open Lean

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


open Verso.Output in
structure LocalContentItem where
  header? : Option HeaderStatus
  dest : String
  linkTexts : Array (String × Html)
  linkTexts_nonempty : linkTexts.size > 0

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

partial def inlineItem? (impls : ExtensionImpls) (xref : TraverseState) (blk : Inline) (contents : Array (Doc.Inline Manual)) : Option LocalContentItem := do
  let impl ← impls.getInline? blk.name
  let id ← blk.id
  let names := impl.localContentItem id blk.data contents
  if h : names.size > 0 then
    let (path, slug) ← xref.externalTags[id]?
    return ⟨none, path.link slug.toString, names, h⟩
  else failure

partial def inlineContents (impls : ExtensionImpls) (xref : TraverseState) (acc : Array LocalContentItem) (i : Doc.Inline Manual) : Array LocalContentItem := Id.run do
  match i with
  | .concat xs | .footnote _ xs | .link xs _ | .bold xs | .emph xs =>
    let mut acc := acc
    for x in xs do
      acc := inlineContents impls xref acc x
    acc
  | .other inl is =>
    let mut acc := acc
    if let some item := inlineItem? impls xref inl is then
      acc := acc.push item
    for i in is do
      acc := inlineContents impls xref acc i
    acc
  | .image .. | .linebreak .. | .math .. | .code .. | .text ..=> acc

partial def blockItem? (impls : ExtensionImpls) (xref : TraverseState) (blk : Block) (contents : Array (Doc.Block Manual)) : Option LocalContentItem := do
  let impl ← impls.getBlock? blk.name
  let id ← blk.id
  let names := impl.localContentItem id blk.data contents
  if h : names.size > 0 then
    let (path, slug) ← xref.externalTags[id]?
    return ⟨none, path.link slug.toString, names, h⟩
  else failure

partial def blockContents (impls : ExtensionImpls) (xref : TraverseState) (acc : Array LocalContentItem) (b : Doc.Block Manual) : Array LocalContentItem := Id.run do
  match b with
  | .para txt =>
    let mut acc := acc
    for i in txt do
      acc := inlineContents impls xref acc i
    acc
  | .code .. => acc
  | .concat xs | .blockquote xs =>
    let mut acc := acc
    for x in xs do
      acc := blockContents impls xref acc x
    acc
  | .ul xs | .ol _ xs =>
    let mut acc := acc
    for x in xs do
      for y in x.contents do
        acc := blockContents impls xref acc y
    acc
  | .dl xs =>
    let mut acc := acc
    for x in xs do
      for i in x.term do
        acc := inlineContents impls xref acc i
      for y in x.desc do
        acc := blockContents impls xref acc y
    acc
  | .other blk bs =>
    let mut acc := acc
    if let some item := blockItem? impls xref blk bs then
      acc := acc.push item
    for b in bs do
      acc := blockContents impls xref acc b
    acc

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

inductive SubpartSpec where
  | none
  | depth : Nat → SubpartSpec
  | all
deriving DecidableEq, Ord, Repr

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
    (opts : Html.Options Manual (ReaderT ExtensionImpls IO)) (ctxt : TraverseContext) (xref : TraverseState)
    (p : Part Manual) (sectionNumPrefix : Option String)
    (includeTitle : Bool) (includeSubparts : SubpartSpec) (fromLevel : Nat) :
    StateT (Code.Hover.State Html) (ReaderT ExtensionImpls IO) (Array LocalContentItem) := do
  let sectionNumPrefix := sectionNumPrefix <|> sectionString ctxt
  let mut out := #[]

  if includeTitle then
    let (html, _) ← p.title.mapM (Manual.toHtml opts ctxt xref {} {} {} ·) |>.run {}
    let partDest : Option LocalContentItem := do
      let m ← p.metadata
      let id ← m.id
      let (path, slug) ← xref.externalTags[id]?
      let num := sectionString ctxt |>.map (withoutPrefix · sectionNumPrefix)

      return ⟨some ⟨fromLevel, num⟩, path.link slug.toString, #[(p.titleString, html)], by simp⟩
    out := out ++ partDest.toArray

  if includeSubparts > .none then
    for b in p.content do
      out := blockContents (← readThe ExtensionImpls) xref out b

  if includeSubparts > .none then
    for p' in p.subParts do
      -- In the recursive cases, `includeTitle` is `true` because all the sections and subsections
      -- on the page should be listed in the local ToC
      out := out ++ (← localContentsCore opts (ctxt.inPart p') xref p' sectionNumPrefix true includeSubparts.decr (fromLevel + 1))

  return out
where
  withoutPrefix (str : String) (prefix? : Option String) : String :=
    prefix?.bind (str.dropPrefix? · |>.map Substring.toString) |>.getD str

def localContents
    (opts : Html.Options Manual (ReaderT ExtensionImpls IO)) (ctxt : TraverseContext) (xref : TraverseState)
    (p : Part Manual)
    (sectionNumPrefix : Option String := none)
    (includeTitle : Bool := true) (includeSubparts : SubpartSpec := .all) (fromLevel : Nat := 0) :
    StateT (Code.Hover.State Html) (ReaderT ExtensionImpls IO) (Array LocalContentItem) :=
  uniquifyLocalItems <$>
    localContentsCore opts ctxt xref p
      (sectionNumPrefix := sectionNumPrefix)
      (includeTitle := includeTitle)
      (includeSubparts := includeSubparts)
      (fromLevel := fromLevel)
