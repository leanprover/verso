/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import Lean.Data.Json.FromToJson

import Verso
import Verso.Genre.Manual

open Verso Genre Manual
open Verso.Doc.Elab
open Lean (ToJson FromJson)

namespace DemoTextbook.Exts.Index


/-

An index has the following components:
 1. During elaboration, index entries are saved in the document AST
 2. During the traversal pass, entries are collected and replaced with unique link targets and/or
    labels, and the index table is assembled
 3. During rendering, the index table is inserted where desired

-/

structure Entry where
  term : Doc.Inline Manual
  /-- A more specific sub-entry, if applicable.

  In a traditional index, this will create output like:

  normalization
    of terms, 22
    of casts, 324

  (here "of terms" and "of casts" would be the sub-entries)
  -/
  subterm : Option String := none -- TODO make into array of inlines

  /-- Use a different index than the default one for this entry? -/
  index : Option String := none

deriving BEq, Hashable, ToJson, FromJson

structure See where
  entry : Entry
  /--
  If `true`, the pointer is for additional information (e.g. "see also"). Otherwise, it's a
  replacement.
  -/
  seeAlso : Bool := false
end Index

instance [BEq α] [Hashable α] : Hashable (Lean.HashSet α) where
  hash xs := hash xs.toArray

structure Index where
  entries : Lean.HashSet (Index.Entry × InternalId)
deriving BEq, Hashable

instance : ToJson Index where
  toJson | ⟨entries⟩ => ToJson.toJson entries.toArray

instance : FromJson Index where
  fromJson? v := do
    let entries : Array (Index.Entry × InternalId) ← FromJson.fromJson? v
    pure ⟨Lean.HashSet.insertMany {} entries⟩

def Inline.index : Inline where
  name := `DemoTextbook.Exts.index

def indexState := `DemoTextbook.Exts.Index

def index.descr : InlineDescr where
  traverse id data _contents := do
    -- TODO use internal tags in the first round to respect users' assignments (cf part tag assignment)
    let _ ← Verso.Genre.Manual.externalTag id "--index"
    match FromJson.fromJson? data with
    | .error err =>
      logError err
      return none
    | .ok (entry : Index.Entry) =>
      let ist : Option (Except String Index) := (← get).get? indexState
      match ist with
      | some (.error err) => logError err; return none
      | some (.ok v) => modify (·.set indexState {v with entries := v.entries.insert (entry, id)})
      | none => modify (·.set indexState {entries := (Lean.HashSet.empty.insert (entry, id)) : Index})
      pure none
  toTeX :=
    some <| fun go id _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _go id inl _content => do
      let some t := (←read).2.2.externalTags.find? id
        | panic! s!"Untagged index target with data {inl}"
      return {{<span id={{t}}></span>}}

def index (args : Array (Doc.Inline Manual)) (subterm : Option String := none) (index : Option String := none) : Doc.Inline Manual :=
  let entry : Index.Entry := {term := .concat args, subterm, index}
  Doc.Inline.other {Inline.index with data := ToJson.toJson entry} #[]

def Block.theIndex : Block where
  name := `DemoTextbook.Exts.theIndex

structure RenderedEntry where
  sorting : String
  term : Doc.Inline Manual
  links : Array InternalId
  subterms : Array (String × Doc.Inline Manual × Array InternalId)

open Verso.Output Html in
def RenderedEntry.toHtml [Monad m] (inlineHtml : Doc.Inline Manual → Doc.Html.HtmlT Manual m Html) (entry : RenderedEntry) : Doc.Html.HtmlT Manual m Html := do
  let termPart ← oneTerm entry.term entry.links
  let subPart ←
    if entry.subterms.size != 0 then
      pure {{<ol>{{ ← entry.subterms.mapM fun (_,t,ls) => ({{<li>{{·}}</li>}}) <$> oneTerm t ls }}</ol>}}
    else pure .empty
  pure <| termPart ++ subPart
where
oneTerm term links := do
  let (_, _, xref) ← read
  let termHtml ← inlineHtml term
  match links.size with
  | 0 => pure termHtml
  | 1 => pure {{<a href=s!"#{xref.externalTags.find! links[0]!}">{{termHtml}}</a>}}
  | _ =>
    let links := links.mapIdx fun i id =>
      {{<a href=s!"#{xref.externalTags.find! id}"> s!"({i.val})" </a>}}
    pure {{ {{termHtml}} " " {{links}} }}

-- TODO this is probably the wrong comparison. Eventually, this will have to be configurable
-- due to localization.
def RenderedEntry.compare (e1 e2 : RenderedEntry) : Ordering :=
  Ord.compare e1.sorting e2.sorting

partial def sortingKey : Doc.Inline g → String
  | .text str | .code str | .math _ str => str
  | .linebreak _ => " "
  | .emph i | .bold i | .concat i | .link i _ => String.join (i.toList.map sortingKey)
  | .image .. | .other .. | .footnote .. => ""


def Index.render (index : Index) : Array RenderedEntry := Id.run do
  -- First consolidate entries
  let mut terms : Lean.HashMap String (Doc.Inline Manual × Array InternalId × Lean.HashMap String (Doc.Inline Manual × Array InternalId)) := {}
  for (e, id) in index.entries do
    let key := sortingKey e.term
    let (term, links, subterms) := terms.findD key (e.term, #[], {})
    if let some sub := e.subterm then
      let (term', links') := subterms.findD sub (.text sub, #[])
      terms := terms.insert key (term, links, subterms.insert sub (term', links'.push id))
    else
      terms := terms.insert key (term, links.push id, subterms)
  -- Then build the sequential structure
  let mut entries := #[]
  for (key, (term, links, subterms)) in terms.toArray do
    let mut subs := #[]
    for (key', (term', links')) in subterms.toArray do
      subs := subs.push (key', term', links')
    entries := entries.push {
      sorting := key,
      term := term,
      links := links,
      subterms := subs.qsort (·.1 < ·.1)
    }

  entries.qsort (RenderedEntry.compare · · |>.isLE)

def theIndex.descr : BlockDescr where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := some indexCss
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI goB _ _ content => do
      let ist : Option (Except String Index) := (← read).2.2.get? indexState
      match ist with
      | some (.error err) =>
        Verso.Doc.Html.HtmlT.logError err
        return .empty
      | none =>
        Verso.Doc.Html.HtmlT.logError "Index data not found"
        return .empty
      | some (.ok v) =>
        return {{<ol class="theIndex">{{← v.render.mapM (do return {{<li>{{← ·.toHtml goI}}</li>}})}}</ol>}}
where
  indexCss := r###"
    ol.theIndex {
      column-width: 12em;
      list-style-type: none;
      padding-left: 0;
    }

    ol.theIndex ol {
      list-style-type: none;
      padding-left: 1em;
    }

    ol.theIndex li {
      break-inside: avoid;
    }
    "###

def theIndex (index : Option String := none) : Doc.Block Manual :=
  Doc.Block.other {Block.theIndex with data := ToJson.toJson index} #[]

-- @[part_command paragraph]
-- def theIndex : PartCommand
--   | stx => do
--     let args ← stxs.mapM elabInline
--     let val ← ``(Inline.other Inline.index #[ $[ $args ],* ])
--     pure #[val]
