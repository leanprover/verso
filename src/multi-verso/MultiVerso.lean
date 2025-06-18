/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json

import Std.Data.TreeMap
import Std.Data.HashSet

import MultiVerso.InternalId
import MultiVerso.Link
import MultiVerso.Manifest
import MultiVerso.Path
import MultiVerso.Slug

open Std
open Lean

namespace Verso.Multi

/--
A documented object, described in specific locations in the document.
-/
structure Object where
  /--
  The canonical string name used to construct a cross-reference to this object, also from external
  sites. Should be stable over time.
  -/
  canonicalName : String
  /-- Extra data that can be used e.g. for rendering a domain index -/
  data : Json := .null
  /-- The IDs of the description site(s) -/
  ids : HashSet InternalId := {}
deriving Inhabited

open Format in
instance : Repr Object where
  reprPrec v _ :=
    let {canonicalName, data, ids} := v
    nest 2 <| group <| line.joinSep [
      text "{",
      nest 2 <| group <| "canonicalName :=" ++ line ++ repr canonicalName ++ ",",
      nest 2 <| group <| "data :=" ++ line ++ group ("json%"++ data.render) ++ ",",
      nest 2 <| group <| "ids :=" ++ line ++ group (line.joinSep ("{" :: ids.toList.map toString) ++ "}"),
      text "}"
    ]

instance : BEq Object where
  beq
    | {canonicalName := n1, data := d1, ids := i1}, {canonicalName := n2, data := d2, ids := i2} =>
      n1 == n2 &&
      d1 == d2 &&
      i1.size == i2.size && i1.fold (init := true) (fun soFar v => soFar && i2.contains v)

def Object.addId (id : InternalId) (object : Object) : Object :=
  {object with ids := object.ids.insert id}

def Object.setData (data : Json) (object : Object) : Object :=
  {object with data := data}

def Object.modifyData (f : Json → Json) (object : Object) : Object :=
  {object with data := f object.data}

/--
A particular category of documentable objects.
-/
structure Domain where
  /-- The objects in the domain, categorized by their canonical names. -/
  objects : TreeMap String Object compare := {}
  /-- The objects in the domain, categorized by their internal IDs. -/
  objectsById : TreeMap InternalId (HashSet String) := {}
  title : Option String := none
  description : Option String := none
deriving Inhabited, Repr

instance : BEq Domain where
  beq
    | ⟨d1, byId1, t1, desc1⟩, ⟨d2, byId2, t2, desc2⟩ =>

      d1.size == d2.size && d1.all (fun k v => d2[k]?.isEqSome v) &&
      byId1.size == byId2.size && byId1.all (fun k v =>
        if let some xs := byId2[k]? then
          xs.size == v.size && xs.all v.contains
        else false) &&
      t1 == t2 &&
      desc1 == desc2

def Domain.insertId (canonicalName : String) (id : InternalId) (domain : Domain) : Domain :=
  { domain with
    objects := domain.objects.alter canonicalName (·.getD {canonicalName} |>.addId id)
    objectsById := domain.objectsById.alter id (·.getD {} |>.insert canonicalName) }

def Domain.setData  (canonicalName : String) (data : Json) (domain : Domain) : Domain :=
  { domain with objects := domain.objects.alter canonicalName (·.getD {canonicalName} |>.setData data) }

def Domain.modifyData  (canonicalName : String) (f : Json → Json) (domain : Domain) : Domain :=
  { domain with objects := domain.objects.alter canonicalName (·.getD {canonicalName} |>.modifyData f) }

def Domain.get? (canonicalName : String) (domain : Domain) : Option Object :=
  domain.objects[canonicalName]?

def xrefJson {Links} {valid} [GetElem? Links InternalId Link valid]
    (domains : NameMap Domain) (links : Links) : Json := Id.run do
  let mut out : Json := Json.mkObj []
  for (n, dom) in domains do
    out := out.setObjVal! n.toString <| Json.mkObj [
      ("title", Json.str <| dom.title.getD n.toString),
      ("description", dom.description.map Json.str |>.getD Json.null),
      ("contents", Json.mkObj <| dom.objects.toList.map fun (x, y) =>
        (x, ToJson.toJson <| y.ids.toList.filterMap (jsonRef y.data <$> links[·]?)))]
  pure out

where
  jsonRef (data : Json) (ref : Link) : Json :=
    Json.mkObj [("address", ref.path.link), ("id", ref.htmlId.toString), ("data", data)]

structure RefObject where
  link : Link
  data : Json

open Format in
instance : Repr RefObject where
  reprPrec v _ :=
    let {link, data} := v
    nest 2 <| group <| line.joinSep [
      text "{",
      nest 2 <| group <| "link :=" ++ line ++ repr link ++ ",",
      nest 2 <| group <| "data :=" ++ line ++ group ("json%"++ data.render) ++ ",",
      text "}"
    ]

structure RefDomain where
  title : Option String := none
  description : Option String := none
  contents : HashMap String (Array RefObject)
deriving Inhabited, Repr


def fromXrefJson (json : Json) : Except String (NameMap RefDomain) := do
  let json ← json.getObj?
  let mut out := {}
  let json := json.toArray
  for ⟨domainName, v⟩ in json do
    let domainName := domainName.toName
    let title ← v.getObjValAs? (Option String) "title"
    let description ← v.getObjValAs? (Option String) "title"
    let contentsJson ← v.getObjVal? "contents"
    let contentsJson ← contentsJson.getObj?
    let mut contents : HashMap String (Array RefObject) := {}
    for ⟨canonicalName, v⟩ in contentsJson.toArray do
      let .arr v := v
        | throw s!"Expected JSON array, got {v.compress}"
      let v ← v.mapM fun x => do
        let address ← x.getObjValAs? String "address"
        let address := address.stripPrefix "/" |>.stripSuffix "/" |>.splitOn "/" |>.toArray
        let htmlId ← x.getObjValAs? String "id"
        let data ← x.getObjVal? "data"
        pure {link := {path := address, htmlId := htmlId.sluggify}, data : RefObject}
      contents := contents.insert canonicalName v
    out := out.insert domainName {title, description, contents}
  return out
