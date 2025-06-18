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

set_option linter.missingDocs true

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

/--
Registers the fact that the provided `id` refers to the object.
-/
def Object.addId (id : InternalId) (object : Object) : Object :=
  {object with ids := object.ids.insert id}

/--
Sets the `data` field of the object, replacing existing data.
-/
def Object.setData (data : Json) (object : Object) : Object :=
  {object with data := data}

/--
Modifies the `data` field of the object.
-/
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
  /--
  An explanatory title for clients of the domain.
  -/
  title : Option String := none
  /--
  A description for clients of the domain.
  -/
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

/--
Registers the fact that the given ID refers to the object with the given canonical name.
-/
def Domain.insertId (canonicalName : String) (id : InternalId) (domain : Domain) : Domain :=
  { domain with
    objects := domain.objects.alter canonicalName (·.getD {canonicalName} |>.addId id)
    objectsById := domain.objectsById.alter id (·.getD {} |>.insert canonicalName) }

/--
Sets the `data` field of the object with the given canonical name, replacing existing data.
-/
def Domain.setData  (canonicalName : String) (data : Json) (domain : Domain) : Domain :=
  { domain with objects := domain.objects.alter canonicalName (·.getD {canonicalName} |>.setData data) }

/--
Modifies the `data` field of the object with the given canonical name.
-/
def Domain.modifyData  (canonicalName : String) (f : Json → Json) (domain : Domain) : Domain :=
  { domain with objects := domain.objects.alter canonicalName (·.getD {canonicalName} |>.modifyData f) }

/--
Returns the object with the given canonical name, or `none` if there is no such object.
-/
def Domain.get? (canonicalName : String) (domain : Domain) : Option Object :=
  domain.objects[canonicalName]?

/--
Generates the public cross-reference file for a set of domains.

`links` maps internal IDs to their corresponding URLs.
-/
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

/--
An object loaded from a cross-reference database.
-/
structure RefObject where
  /-- The object's link destination. -/
  link : Link
  /-- Metadata saved for the object. -/
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

/--
Converts a reference object to the official interchange format.
-/
def RefObject.toJson (object : RefObject) : Json :=
  json%{"address": $object.link.path.link, "id": $object.link.htmlId.toString, "data": $object.data}

/--
A domain loaded from a cross-reference database.
-/
structure RefDomain where
  /--
  The domain's title field.
  -/
  title : Option String := none
  /--
  The domain's description field.
  -/
  description : Option String := none
  /--
  A mapping from canonical names to reference locations.
  -/
  contents : HashMap String (Array RefObject)
deriving Inhabited, Repr

/--
Converts a reference domain to the official interchange format.
-/
def RefDomain.toJson (domain : RefDomain) : Json :=
  let contents : Json := .mkObj <| domain.contents.toList.map fun (k, v) => (k, .arr <| v.map (·.toJson))
  json%{
    "title": $domain.title,
    "description": $domain.description,
    "contents": $contents
  }

/--
Loads a set of reference domains from a cross-reference database in JSON format.
-/
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

private def normPath (path : System.FilePath) : System.FilePath :=
  System.mkFilePath <| removeSpecial path.components
where
  removeSpecial xs := remove' xs.reverse |>.reverse
  remove'
    | [] => []
    | [x] => [x]
    | ".." :: _ :: xs => remove' xs
    | "." :: xs => remove' xs
    | x :: xs => x :: remove' xs


private partial def findProject (path : System.FilePath) : IO System.FilePath := do
  if path.isRelative then
    find' <| normPath <| (← IO.currentDir) / path
  else
    find' <| normPath <| (← IO.currentDir) / path
where
  find' (path : System.FilePath) : IO System.FilePath := do
    if !(← path.pathExists) then throw <| IO.userError s!"Not found: {path}"
    if (← path.isDir) then
      if (← (path / "lean-toolchain").pathExists) then return path
    if let some parent := path.parent then
      return (← findProject parent)
    throw <| IO.userError "No 'lean-toolchain' found in a parent directory"

private def fetchRemote (project : System.FilePath) (url : String) : IO (NameMap RefDomain) := do
  let json ←
    IO.Process.run {
      cmd := "curl",
      args := #[url]
      cwd := project
    }
  let json ← Json.parse json |> IO.ofExcept
  fromXrefJson json |> IO.ofExcept

private def fetchFile (project : System.FilePath) (file : System.FilePath) : IO (NameMap RefDomain) := do
  let json ← IO.FS.readFile (project / file)
  let json ← Json.parse json |> IO.ofExcept
  fromXrefJson json |> IO.ofExcept

private def getConfig (project : System.FilePath) (configFile : Option System.FilePath) : IO Config := do
    let configFile : System.FilePath :=
      if let some f := configFile then f
      else project / "verso-sources.json"
    let configJson ← IO.FS.readFile configFile
    let configJson ← Json.parse configJson |> IO.ofExcept
    Config.fromJson? configJson |> IO.ofExcept

/--
Updates the remote Verso data, fetching according to the configuration.
-/
def updateRemotes (manual : Bool) (configFile : Option System.FilePath) (logVerbose : String → IO Unit) : IO (HashMap String (String × (NameMap RefDomain))) := do
  let project ← findProject "."
  let config ← getConfig project configFile

  IO.FS.createDirAll config.outputDir
  let manifestPath := config.outputDir / "verso-xref-manifest.json"
  let xrefsPath := config.outputDir / "verso-xref.json"
  let mut values : HashMap String (String × (NameMap RefDomain)) := {}
  let mut metadata : HashMap String RemoteMeta := {}
  let oldManifest : Manifest ←
    try
      let old ← IO.ofExcept <| Json.parse (← IO.FS.readFile manifestPath) >>= Manifest.fromJson?
      logVerbose s!"Loaded existing manifest from {manifestPath}"
      pure old
    catch
      | e =>
        logVerbose s!"Couldn't load manifest from {manifestPath}: {e}"
        pure {config with metadata := {}}
  let oldXrefs : HashMap String (NameMap RefDomain) ←
    try
      let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile xrefsPath) >>= Json.getObj?
      let json := json.toArray
      json.foldlM (init := ({} : HashMap String (NameMap RefDomain))) fun xs ⟨k, v⟩ =>
        xs.insert k <$> IO.ofExcept (fromXrefJson v)
    catch | _ => pure {}
  for (name, {root, updateFrequency, sources}) in config.sources do
    let mut found : Option (NameMap RefDomain) := none
    let lastUpdated := oldManifest.metadata[name]? |>.map (·.lastUpdated)
    if let some prior := lastUpdated then
      match updateFrequency with
      | .days d =>
        if compare (prior + d) (← Std.Time.PlainDateTime.now) |>.isGE then
          found := oldXrefs[name]?
          if let some v := found then
            logVerbose s!"Used saved xref database for {name}, next update at {prior + d |>.toDateTimeString}"
            values := values.insert name (root, v)
            metadata := metadata.insert name { lastUpdated := (← Std.Time.PlainDateTime.now) }
            continue
      | .manual =>
        -- If this is an automatic update, attempt to use the saved value
        unless manual do
          found := oldXrefs[name]?
          if let some v := found then
            logVerbose s!"Used saved xref database for {name}, which is to be manually updated"
            values := values.insert name (root, v)
            metadata := metadata.insert name { lastUpdated := (← Std.Time.PlainDateTime.now) }
            continue

    let sources := if sources.isEmpty then [.default] else sources

    for s in sources do
      try
        match s with
        | .default =>
          let out ← fetchRemote project (root ++ "/" ++ "xref.json")
          found := some out
          break
        | .localOverride f =>
          let out ← fetchFile project f
          found := some out
          break
        | .remoteOverride url =>
          let out ← fetchRemote project url
          found := some out
          break
      catch | _ => continue
    if let some v := found then
      values := values.insert name (root, v)
      metadata := metadata.insert name { lastUpdated := (← Std.Time.PlainDateTime.now) }
    else throw <| IO.userError s!"No source found for {name}"

  let manifest : Manifest := {config with metadata}
  IO.FS.writeFile manifestPath (manifest.toJson.render.pretty 78)
  let valuesJson : Json := .mkObj <| values.toList.map fun (k, v) =>
    (k, .mkObj <| v.snd.toList.map fun ⟨d, o⟩ => (d.toString, o.toJson))
  IO.FS.writeFile xrefsPath (valuesJson.render.pretty 78)
  return values
