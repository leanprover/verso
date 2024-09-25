/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import Lean.Data.Json.FromToJson
import Std.Data.HashMap
import Std.Data.HashSet

import VersoManual.Basic

open Verso Genre Manual
open Verso.Doc.Elab
open Lean (ToJson FromJson)
open Std (HashMap HashSet)

namespace Verso.Genre.Manual.Index


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
  subterm : Option (Doc.Inline Manual) := none

  /-- Use a different index than the default one for this entry? -/
  index : Option String := none

deriving BEq, Hashable, ToJson, FromJson, Ord

instance instLtEntry : LT Entry where
  lt x y := Ord.compare x y = .lt

instance : DecidableRel (@LT.lt Entry instLtEntry) :=
  fun _ _ => inferInstance

structure See where
  source : Doc.Inline Manual
  target : Doc.Inline Manual
  subTarget : Option (Doc.Inline Manual)
  /--
  If `true`, the pointer is for additional information (e.g. "see also"). Otherwise, it's a
  replacement.
  -/
  also : Bool := false
  index : Option String := none
deriving BEq, Hashable, ToJson, FromJson, Ord

instance : LT See where
  lt x y := Ord.compare x y = .lt

end Index


structure Index where
  entries : HashSet (Index.Entry × InternalId) := {}
  see : HashSet Index.See := {}

instance : ToJson Index where
  toJson | ⟨entries, see⟩ => ToJson.toJson (entries.toArray.qsort cmpEntry, see.toArray.qsort (· < ·))
where
  cmpEntry | (e1, id1), (e2, id2) => e1 < e2 || (e1 == e2 && id1 < id2)

instance : FromJson Index where
  fromJson? v := do
    let ((entries : Array _), (sees : Array _)) ← FromJson.fromJson? v
    pure ⟨HashSet.insertMany {} entries, HashSet.insertMany {} sees⟩

def Inline.index : Inline where
  name := `Verso.Genre.Manual.index

def indexState := `Verso.Genre.Manual.index

def index (args : Array (Doc.Inline Manual)) (subterm : Option String := none) (index : Option String := none) : Doc.Inline Manual :=
  let entry : Index.Entry := {term := .concat args, subterm := subterm.map Doc.Inline.text, index}
  Doc.Inline.other {Inline.index with data := ToJson.toJson entry} #[]

/-- Adds an internal identifier as a target for a given index entry -/
def Index.addEntry [Monad m] [MonadState TraverseState m] [MonadLiftT IO m] [MonadReaderOf TraverseContext m]
    (id : InternalId) (entry : Index.Entry) : m Unit := do
  let ist : Option (Except String Index) := (← get).get? indexState
  match ist with
  | some (.error err) => logError err
  | some (.ok v) => modify (·.set indexState {v with entries := v.entries.insert (entry, id)})
  | none => modify (·.set indexState {entries := (HashSet.empty.insert (entry, id)) : Index})

@[inline_extension index]
def index.descr : InlineDescr where
  traverse id data _contents := do
    -- TODO use internal tags in the first round to respect users' assignments (cf part tag assignment)
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path "--index"
    match FromJson.fromJson? data with
    | .error err =>
      logError err
      return none
    | .ok (entry : Index.Entry) =>
      Index.addEntry id entry
      pure none
  toTeX :=
    some <| fun go _id _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _go id inl _content => do
      let some (_, t) := (← read).traverseState.externalTags.get? id
        | panic! s!"Untagged index target with data {inl}"
      return {{<span id={{t}}></span>}}

def Inline.see : Inline where
  name := `Verso.Genre.Manual.see

def see (args : Array (Doc.Inline Manual)) (target : String) (subterm : Option String := none) (index : Option String := none) : Doc.Inline Manual :=
  let data : Index.See := {source := .concat args, target := .text target, subTarget := subterm.map .text, also := false, index}
  Doc.Inline.other {Inline.see with data := ToJson.toJson data} #[]

def seeAlso (args : Array (Doc.Inline Manual)) (target : String) (subterm : Option String := none) (index : Option String := none) : Doc.Inline Manual :=
  let data : Index.See := {source := .concat args, target := .text target, subTarget := subterm.map .text, also := true, index}
  Doc.Inline.other {Inline.see with data := ToJson.toJson data} #[]

@[inline_extension see]
def see.descr : InlineDescr where
  traverse _id data _contents := do
    match FromJson.fromJson? data with
    | .error err =>
      logError err
      return none
    | .ok (see : Index.See) =>
      let ist : Option (Except String Index) := (← get).get? indexState
      match ist with
      | some (.error err) => logError err; return none
      | some (.ok v) => modify (·.set indexState {v with see := v.see.insert see})
      | none => modify (·.set indexState {entries := {}, see := (HashSet.empty.insert see) : Index})
      pure none
  toTeX :=
    some <| fun _ _ _ _ => do
      pure <| .seq #[]
  toHtml :=
    some <| fun _go _id _inl _content => pure .empty

def seeAlso.descr : InlineDescr := see.descr

def Block.theIndex : Block where
  name := `Verso.Genre.Manual.theIndex

structure RenderedEntryId where
  toString : String
deriving ToJson, FromJson, Repr

structure RenderedEntry where
  id : RenderedEntryId -- Relying on name mangling to make this unique for now
  sorting : String
  term : Doc.Inline Manual
  links : Array InternalId
  subterms : Array (String × RenderedEntryId × Doc.Inline Manual × Array InternalId)
  see : Array (RenderedEntryId × Bool × Doc.Inline Manual)
deriving ToJson

open Verso.Output Html in
def RenderedEntry.toHtml [Monad m] (inlineHtml : Doc.Inline Manual → Doc.Html.HtmlT Manual m Html) (entry : RenderedEntry) : Doc.Html.HtmlT Manual m Html := do
  let termPart ← oneTerm entry.id entry.term entry.links
  let subPart ←
    if entry.subterms.size != 0 || entry.see.size != 0 then
      pure {{
        <ol>
          {{ ← entry.subterms.mapM fun (_,rid,t,ls) => ({{<li>{{·}}</li>}}) <$> oneTerm rid t ls }}
          {{ ← entry.see.mapM fun (rid, also, txt) => do
            return {{
              <li>
                s!"See {if also then "also " else ""}"
                <a href=s!"#{rid.toString}">{{← inlineHtml txt}}</a>
              </li>
            }}
          }}
        </ol>
      }}
    else pure .empty
  pure <| termPart ++ subPart
where
  oneTerm id term links : Doc.Html.HtmlT Manual m Html := open Doc.Html HtmlT in do
    let xref ← state
    let termHtml ← ({{<span id={{id.toString}}>{{·}}</span>}}) <$> inlineHtml term
    match h : links.size with
    | 0 => pure termHtml
    | 1 =>
      if let some (path, htmlId) := xref.externalTags[links[0]]? then
        let addr := String.join (path.map ("/" ++ ·) |>.toList)
        pure {{<a href=s!"{addr}#{htmlId}">{{termHtml}}</a>}}
      else
        HtmlT.logError s!"No external tag for {id.toString}"
        pure .empty
    | _ =>
      let links ← links.mapIdxM fun i id => do
        if let some (path, htmlId) := xref.externalTags[id]? then
          let addr := String.join (path.map ("/" ++ ·) |>.toList)
          pure {{" " <a href=s!"{addr}#{htmlId}"> s!"({i.val})" </a>}}
        else
          HtmlT.logError s!"No external tag for {id}"
          pure .empty

      pure {{ {{termHtml}} {{links}} }}

-- TODO this is probably the wrong comparison. Eventually, this will have to be configurable
-- due to localization.
def RenderedEntry.compare (e1 e2 : RenderedEntry) : Ordering :=
  Ord.compare e1.sorting e2.sorting

partial def sortingKey : Doc.Inline g → String
  | .text str | .code str | .math _ str => str
  | .linebreak _ => " "
  | .emph i | .bold i | .concat i | .link i _ => String.join (i.toList.map sortingKey)
  | .image .. | .other .. | .footnote .. => ""

inductive IndexCat where
  | symbolic
  | digit
  | letter (c : Char)
deriving BEq

instance : Hashable IndexCat where
  hash
    | .symbolic => 3
    | .digit => 5
    | .letter c => mixHash 7 (hash c.toNat)

open Output.Html in
def IndexCat.header : IndexCat → Output.Html
  | .symbolic => "Symbols"
  | .digit => "0–9"
  | .letter c => c.toUpper.toString

def IndexCat.fromString (str : String) : IndexCat :=
  match str.get? 0 with
  | none => .symbolic
  | some c =>
    if c.isAlpha then .letter c.toUpper
    else if c.isDigit then .digit
    else .symbolic

def IndexCat.id : IndexCat → String
  | .symbolic => "#!%"
  | .digit => "0–9"
  | .letter c => c.toUpper.toString

def IndexCat.compare : IndexCat → IndexCat → Ordering
  | .symbolic, .symbolic => .eq
  | .symbolic, _ => .lt
  | .digit, .symbolic => .gt
  | .digit, .digit => .eq
  | .digit, _ => .lt
  | .letter c, .letter c' => Ord.compare c c'
  | .letter _, _ => .gt

def Index.render (index : Index) : Array (IndexCat × Array RenderedEntry) := Id.run do
  -- First consolidate entries
  let mut usedIds := {}
  let mut terms : HashMap String (Doc.Inline Manual × RenderedEntryId × Array InternalId × HashMap String (Doc.Inline Manual × RenderedEntryId × Array InternalId)) := {}
  for (e, id) in index.entries do
    let key := sortingKey e.term

    let (term, rid, links, subterms) ←
      if let some vals := terms[key]? then pure vals
      else
        let defaultRId := key.sluggify.unique usedIds
        usedIds := usedIds.insert defaultRId
        (e.term, ⟨s!"---entry-{defaultRId}"⟩, #[], {})

    if let some sub := e.subterm then
      let k := sortingKey sub
      let (k', term', rid', links') ←
        if let some e := subterms[k]? then pure (k, e)
        else
          let defaultRId := "{key}---{k}".sluggify.unique usedIds
          usedIds := usedIds.insert defaultRId
          (k, sub, ⟨s!"---entry-{defaultRId}"⟩, #[])
      terms := terms.insert key (term, rid, links, subterms.insert k' (term', rid', links'.push id))
    else
      terms := terms.insert key (term, rid, links.push id, subterms)

  -- Then find internal xrefs
  let mut xrefs : HashMap String (Array (RenderedEntryId × Bool × Doc.Inline Manual)) := {}
  for {source, target, subTarget, also, ..} in index.see do
    let some (_, tgtId, _, subs) := terms[sortingKey target]?
      | continue
    let key := sortingKey source
    let old := xrefs.getD key #[]

    if let some st := subTarget then
      let linkText := Doc.Inline.concat #[target, .text ";", st]
      let some (_, subTgtId, _) := subs[sortingKey st]?
        | continue
      xrefs := xrefs.insert key <| old.push (subTgtId, also, linkText)
    else
      xrefs := xrefs.insert key <| old.push (tgtId, also, target)

  -- Then build the sequential structure
  let mut entries := #[]
  for (key, (term, rid, links, subterms)) in terms.toArray do
    let mut subs := #[]
    for (key', (term', rid', links')) in subterms.toArray do
      subs := subs.push (key', rid', term', links')
    entries := entries.push {
      id := rid,
      sorting := key,
      term := term,
      links := links,
      subterms := subs.qsort (·.1 < ·.1),
      see := xrefs.getD key #[] |>.qsort (sortingKey ·.2.2 < sortingKey ·.2.2)
    }

  entries := entries.qsort (RenderedEntry.compare · · |>.isLE)

  let grouped :=
    entries.groupByKey (IndexCat.fromString <| ·.2)
      |>.toArray
      |>.qsort (·.1.compare ·.1 |>.isLE)

  pure grouped


def theIndex (index : Option String := none) : Doc.Block Manual :=
  Doc.Block.other {Block.theIndex with data := ToJson.toJson index} #[]

@[block_extension theIndex]
def theIndex.descr : BlockDescr where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [indexCss]
  toHtml :=
    open Verso.Output.Html Doc.Html HtmlT in
    some <| fun goI _goB _ _ _content => do
      let ist : Option (Except String Index) := (← state).get? indexState
      match ist with
      | some (.error err) =>
        Verso.Doc.Html.HtmlT.logError err
        return .empty
      | none =>
        Verso.Doc.Html.HtmlT.logError "Index data not found"
        return .empty
      | some (.ok v) =>
        let r := v.render
        let out ← r.mapM fun (cat, xs) => do
          let h := (← read).1.headerLevel + 1
          let hdr := Output.Html.tag s!"h{h}" #[("id", s!"---index-hdr-{cat.id}")] (cat.header)
          let xs' ← xs.mapM (fun e => do return {{<li>{{← e.toHtml goI}}</li>}})
          return {{<div class="division">{{hdr ++ {{<ol>{{xs'}}</ol>}} }}</div>}}
        return {{
          <div class="theIndex">
            <nav>
              <ol>
                {{ r.map fun (cat, _) => {{<li><a href=s!"#---index-hdr-{cat.id}">{{cat.header}}</a></li>}} }}
              </ol>
            </nav>
            {{out}}
          </div>
        }}
where
  indexCss := r###"
    main .theIndex {
      column-width: 14em;
      padding-left: 0;
      font-family: var(--verso-text-font-family);
    }

    main .theIndex nav {
      column-span: all;
    }

    main .theIndex nav ol {
      padding: 0;
    }

    main .theIndex nav ol li {
      display: inline-block;
    }

    main .theIndex nav ol li a {
      margin-left: 0.5em;
      margin-right: 0.5em;
    }

    main .theIndex nav ol li:first-child a {
      margin-left: 0;
    }

    main .theIndex nav ol li + li:before {
      content: "|";
    }

    main .theIndex h1,
    main .theIndex h2,
    main .theIndex h3,
    main .theIndex h4,
    main .theIndex h5,
    main .theIndex h6 {
      margin-top: 0;
    }

    main .theIndex ol {
      list-style-type: none;
    }

    main .theIndex .division > ol {
      padding-left: 0;
    }

   main .theIndex .division > ol > li {
      margin-bottom: 0.5em;
    }

    main .theIndex .division ol ol {
      padding-left: 1em;
    }


    main .theIndex .division {
      break-inside: avoid;
      counter-reset: none;
      max-width: none;
      width: auto;
    }
    "###
