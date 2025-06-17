import Lean.Data.Json

import Std.Data.TreeMap
import Std.Data.HashSet

import MultiVerso.InternalId
import MultiVerso.Link
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
deriving Inhabited

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
