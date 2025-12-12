/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Lean.Data.Json

import Std.Data.TreeMap
import Std.Data.HashSet
import Std.Time.Zoned
import Std.Time.Format

public import MultiVerso.InternalId
public import MultiVerso.Link
public import MultiVerso.NameMap
import MultiVerso.Manifest
import MultiVerso.Path
import MultiVerso.Slug


set_option doc.verso true

open Std
open Lean

set_option linter.missingDocs true

namespace Verso.Multi

/--
A documented object, described in specific locations in the document.
-/
public structure Object where
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

public instance : ToJson Object where
  toJson
    | { canonicalName, data, ids } =>
      json%{ "canonicalName": $canonicalName, "data": $data, "ids": $ids.toArray }

public instance : FromJson Object where
  fromJson? v := do
    let canonicalName ← v.getObjValAs? String "canonicalName"
    let data ← v.getObjVal? "data"
    let ids ← v.getObjValAs? (Array InternalId) "ids"
    let ids := HashSet.ofArray ids
    return { canonicalName, data, ids }

open Format in
public instance : Repr Object where
  reprPrec v _ :=
    let {canonicalName, data, ids} := v
    nest 2 <| group <| line.joinSep [
      text "{",
      nest 2 <| group <| "canonicalName :=" ++ line ++ repr canonicalName ++ ",",
      nest 2 <| group <| "data :=" ++ line ++ group ("json%"++ data.render) ++ ",",
      nest 2 <| group <| "ids :=" ++ line ++ group (line.joinSep ("{" :: ids.toList.map toString) ++ "}"),
      text "}"
    ]

public instance : BEq Object where
  beq
    | {canonicalName := n1, data := d1, ids := i1}, {canonicalName := n2, data := d2, ids := i2} =>
      n1 == n2 &&
      d1 == d2 &&
      i1.size == i2.size && i1.fold (init := true) (fun soFar v => soFar && i2.contains v)

/--
Registers the fact that the provided {name}`id` refers to the object.
-/
public def Object.addId (id : InternalId) (object : Object) : Object :=
  {object with ids := object.ids.insert id}

/--
Sets the {name (full := Object.data)}`data` field of the object, replacing existing data.
-/
public def Object.setData (data : Json) (object : Object) : Object :=
  { object with data := data }

/--
Modifies the {name (full := Object.data)}`data` field of the object.
-/
public def Object.modifyData (f : Json → Json) (object : Object) : Object :=
  {object with data := f object.data}

/--
A particular category of documentable objects.
-/
public structure Domain where
  /-- The objects in the domain, categorized by their canonical names. -/
  objects : TreeMap String Object compare := {}
  /--
  The objects in the domain, categorized by their internal IDs. The values in the map are all
  canonical names for an object with the given ID. In most use cases, without aliasing, the set will
  be a singleton.
  -/
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

public instance : ToJson Domain where
  toJson := private fun
    | {objects, objectsById, title, description} =>
      let objects : Json := objects.foldl (init := Json.mkObj []) fun json name obj => json.setObjVal! name (toJson obj)
      let objectsById : Json := .arr <| objectsById.foldl (init := #[]) fun jsons id names => jsons.push (json%{"key": $id, "names": $names.toArray})
      json%{"objects": $objects, "objectsById": $objectsById, "title": $title, "description": $description}

public instance : FromJson Domain where
  fromJson? v := private do
    let objects ← v.getObjVal? "objects"
    let objects ← objects.getObj?
    let objects ← objects.foldlM (init := ({} : TreeMap String Object _)) fun objs name obj => do
      return objs.insert name (← FromJson.fromJson? obj)
    let objectsById ← v.getObjVal? "objectsById"
    let objectsById ← objectsById.getArr?
    let objectsById ← objectsById.foldlM (init := ({} : TreeMap InternalId (HashSet String))) fun soFar v => do
      let id ← v.getObjValAs? _ "key"
      let names ← v.getObjVal? "names"
      let names : Array String ← FromJson.fromJson? names
      return soFar.insert id (HashSet.ofArray names)
    let title ← v.getObjValAs? _ "title"
    let description ← v.getObjValAs? _ "description"
    return { objects, objectsById, title, description }


private def Domain.structBeq : Domain → Domain → Bool
  | ⟨d1, byId1, t1, desc1⟩, ⟨d2, byId2, t2, desc2⟩ =>
    d1.size == d2.size && d1.all (fun k v => d2[k]?.isEqSome v) &&
    byId1.size == byId2.size && byId1.all (fun k v =>
      if let some xs := byId2[k]? then
        xs.size == v.size && xs.all v.contains
      else false) &&
    t1 == t2 &&
    desc1 == desc2

private unsafe def Domain.fastBeq (x y : Domain) : Bool :=
  if ptrEq x y then true else Domain.structBeq x y

/--
Compares two domains for equality.
-/
@[implemented_by Domain.fastBeq]
private def Domain.beq (x y : Domain) : Bool := Domain.structBeq x y

public instance : BEq Domain where
  beq := private Domain.beq

/--
Returns the canonical names used in {name}`domain`.
-/
public def Domain.canonicalNames (domain : Domain) : Array String :=
  domain.objects.keysArray

/--
Registers the fact that the unique ID {name}`id` refers to the object with the given canonical name.
-/
public def Domain.insertId (canonicalName : String) (id : InternalId) (domain : Domain) : Domain :=
  { domain with
    objects :=
      domain.objects.alter canonicalName fun
        | none => some { canonicalName, ids := {id} }
        | some o => some (o.addId id)
    objectsById :=
      domain.objectsById.alter id fun
        | none => some {canonicalName}
        | some ns => ns.insert canonicalName
  }

/--
Sets the {name (full := Object.data)}`data` field of the object with the given canonical name, replacing existing data.
-/
public def Domain.setData  (canonicalName : String) (data : Json) (domain : Domain) : Domain :=
  { domain with objects := domain.objects.alter canonicalName (·.getD {canonicalName} |>.setData data) }

/--
Modifies the {name (full := Object.data)}`data` field of the object with the given canonical name.
-/
public def Domain.modifyData  (canonicalName : String) (f : Json → Json) (domain : Domain) : Domain :=
  { domain with objects := domain.objects.alter canonicalName (·.getD {canonicalName} |>.modifyData f) }

/--
Returns the object with the given canonical name, or {name}`none` if there is no such object.
-/
public def Domain.get? (canonicalName : String) (domain : Domain) : Option Object :=
  domain.objects[canonicalName]?

public instance : GetElem? Domain String Object (fun dom x => dom.get? x |>.isSome) where
  getElem dom x valid :=
    match h : dom.get? x with
    | none => False.elim <| by simp_all
    | some v => v
  getElem? dom x := dom.get? x

/--
Returns {name}`true` if the domain contains an object with the given canonical name, or {name}`false` otherwise.
-/
public def Domain.contains (canonicalName : String) (domain : Domain) : Bool :=
  domain.objects.contains canonicalName

/--
Generates the public cross-reference file for a set of domains.

{name}`links` maps internal IDs to their corresponding URLs.
-/
public def xrefJson {Links} {valid} [GetElem? Links InternalId Link valid]
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
public structure RefObject where
  /-- The object's link destination. -/
  link : RemoteLink
  /-- Metadata saved for the object. -/
  data : Json
deriving BEq

open Format in
public instance : Repr RefObject where
  reprPrec v _ :=
    let {link, data} := v
    nest 2 <| group <| line.joinSep [
      text "{",
      nest 2 <| group <| "link :=" ++ line ++ repr link ++ ",",
      nest 2 <| group <| "data :=" ++ line ++ group ("json%"++ data.render) ++ ",",
      text "}"
    ]

deriving instance ToJson, FromJson for RefObject

/--
Converts a reference object to the official interchange format.
-/
public def RefObject.toJson (object : RefObject) : Json :=
  json%{"address": $object.link.path.link, "id": $object.link.htmlId.toString, "data": $object.data}

/--
A domain loaded from a cross-reference database.
-/
public structure RefDomain where
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

instance : GetElem? RefDomain String (Array RefObject) fun dom name => name ∈ dom.contents where
  getElem dom name ok := dom.contents[name]'ok
  getElem? dom name := dom.contents[name]?

private def RefDomain.structEq (x y : RefDomain) :=
  let ⟨t1, d1, c1⟩ := x
  let ⟨t2, d2, c2⟩ := y
  t1 == t2 && d1 == d2 &&
  c1.size == c2.size &&
  c1.fold (init := true) fun soFar k v =>
    soFar && c2[k]?.isEqSome v

private unsafe def RefDomain.fastEq (x y : RefDomain) :=
  if ptrEq x y then true
  else structEq x y

/--
Boolean equality of reference domains.
-/
@[implemented_by RefDomain.fastEq]
private def RefDomain.beq := RefDomain.structEq

public instance : BEq RefDomain where
  beq := private RefDomain.beq

/--
Converts a reference domain to the official interchange format.
-/
public def RefDomain.toJson (domain : RefDomain) : Json :=
  let contents : Json := .mkObj <| domain.contents.toList.map fun (k, v) => (k, .arr <| v.map (·.toJson))
  json%{
    "title": $domain.title,
    "description": $domain.description,
    "contents": $contents
  }

public instance : ToJson RefDomain where
  toJson domain :=
    let contents : Json := .mkObj <| domain.contents.toList.map fun (k, v) => (k, .arr <| v.map (toJson ·))
    json%{
      "title": $domain.title,
      "description": $domain.description,
      "contents": $contents
    }

public instance : FromJson RefDomain where
  fromJson? v := do
    let title ← v.getObjValAs? _ "title"
    let description ← v.getObjValAs? _ "description"
    let contents ← v.getObjVal? "contents"
    let contents ← contents.getObj?
    let contents : HashMap String (Array RefObject) ← contents.foldlM (init := {}) fun objs k v => do
      return objs.insert k (← fromJson? v)
    return { title, description, contents }

/--
Loads a set of reference domains from a cross-reference database in JSON format.
-/
public def fromXrefJson (root : String) (json : Json) : Except String (NameMap RefDomain) := do
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
        pure {link := {root, path := address, htmlId := htmlId.sluggify}, data : RefObject}
      contents := contents.insert canonicalName v
    out := out.insert! domainName {title, description, contents}
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

private def fetchRemote (project : System.FilePath) (root : String) (url : String) : IO (NameMap RefDomain) := do
  let json ← do
    let out ← IO.Process.output {
      cmd := "curl",
      args := #["--silent", "--show-error", "--fail", url]
      cwd := project
    }
    if out.exitCode ≠ 0 then throw <| IO.userError out.stderr
    pure out.stdout
  let json ← Json.parse json |> IO.ofExcept
  fromXrefJson root json |> IO.ofExcept

private def fetchFile (project : System.FilePath) (root : String) (file : System.FilePath) : IO (NameMap RefDomain) := do
  let json ← IO.FS.readFile (project / file)
  let json ← Json.parse json |> IO.ofExcept
  fromXrefJson root json |> IO.ofExcept

private def defaultConfigFile (project : System.FilePath) : System.FilePath := project / "verso-sources.json"

/--
Returns {name}`true` if the user has specified a configuration file, or if they haven't and the default file exists.
-/
private def hasConfig (project : System.FilePath) (configFile : Option System.FilePath) : IO Bool := do
  if configFile.isSome then return true
  else defaultConfigFile project |>.pathExists

private def getConfig (project : System.FilePath) (configFile : Option System.FilePath) : IO Config := do
  let configFile : System.FilePath :=
    if let some f := configFile then f
    else defaultConfigFile project
  let configJson ← IO.FS.readFile configFile
  let configJson ← Json.parse configJson |> IO.ofExcept
  match Config.fromJson? configJson with
  | .error e => throw <| IO.userError s!"Error reading {configFile}: {e}"
  | .ok v => pure v

/--
Information about a remote document
-/
public structure RemoteInfo where
  /-- The root of the document's URLs. -/
  root : String
  /-- A short name to show in short links (e.g. "v4.20" or a package name). -/
  shortName : String
  /-- A long name to show in longer links (e.g. "Lean Language Reference version 4.20"). -/
  longName : String
  /-- The documented items in the remote. -/
  domains : Verso.NameMap RefDomain
deriving Repr

public instance : ToJson RemoteInfo where
  toJson := private fun
    | { root, shortName, longName, domains } =>
      let domains := domains.toArray.map fun (x, y) => (x.toString, toJson y)
      let domains : Json := .obj <| .ofArray domains _
      json%{ "root": $root, "shortName": $shortName, "longName": $longName, "domains": $domains }

public instance : FromJson RemoteInfo where
  fromJson? v := private do
    let root ← v.getObjValAs? String "root"
    let shortName ← v.getObjValAs? String "shortName"
    let longName ← v.getObjValAs? String "longName"
    let domains ← v.getObjVal? "domains"
    let domains ← domains.getObj?
    let domains : NameMap RefDomain ← domains.foldlM (init := {}) fun ds (x : String) y => do
      let title ← y.getObjValAs? (Option String) "title"
      let description ← y.getObjValAs? (Option String) "description"
      let contents ← y.getObjVal? "contents"
      let contents ← contents.getObj?
      let contents ← contents.foldlM (init := {}) fun c k v => do
        let v ← fromJson? v
        pure <| c.insert k v
      let x' := x.toName
      return ds.insert! x' { title, description, contents }
    return { root, shortName, longName, domains }

private def RemoteInfo.structBEq (x y : RemoteInfo) : Bool :=
  let ⟨root1, x1, y1, doms1⟩ := x
  let ⟨root2, x2, y2, doms2⟩ := y
  root1 == root2 &&
  x1 == x2 &&
  y1 == y2 &&
  doms1.size == doms2.size &&
  doms1.foldl (init := true) fun soFar k v =>
    soFar && doms2[k.toName]?.isEqSome v

private unsafe def RemoteInfo.fastBEq (x y : RemoteInfo) : Bool :=
  if ptrEq x y then true else RemoteInfo.structBEq x y

instance : Membership Name RemoteInfo where
  mem ri dom := dom ∈ ri.domains

instance : GetElem? RemoteInfo Name RefDomain (fun ri d => d ∈ ri) where
  getElem xs x ok := xs.domains[x]'ok
  getElem? xs x := xs.domains[x]?

/--
Looks up an object in a domain, returning all targets.

Returns {lean type:="Option (Array RefObject)"}`none` if {name}`domain` is not a domain in {name}`remote` or if
no object has {name}`canonicalName` as its canonical name in the domain.
-/
public def RemoteInfo.getDomainObject? (remote : RemoteInfo) (domain : Name) (canonicalName : String) : Option (Array RefObject) := do
  let dom ← remote[domain]?
  dom[canonicalName]?

/--
Boolean equality of information about remote documents.
-/
@[implemented_by RemoteInfo.fastBEq]
private def RemoteInfo.beq (x y : RemoteInfo) : Bool := RemoteInfo.structBEq x y

public instance : BEq RemoteInfo where
  beq := private RemoteInfo.beq

/--
All remote data that was loaded.
-/
public structure AllRemotes where
  /-- The remote data -/
  allRemotes : HashMap String RemoteInfo := {}
deriving Repr

public instance : ToJson AllRemotes where
  toJson v := Id.run do
    let mut val := Json.obj {}
    for (name, info) in v.allRemotes do
      val := val.setObjValAs! name info
    return val

public instance : FromJson AllRemotes where
  fromJson? v := do
    let v ← v.getObj?
    let mut all := {}
    for (name, infoJson) in v do
      all := all.insert name (← fromJson? infoJson)
    return ⟨all⟩

public instance : GetElem AllRemotes String RemoteInfo (fun x y => y ∈ x.allRemotes) where
  getElem x y z := GetElem.getElem x.allRemotes y z

public instance : GetElem? AllRemotes String RemoteInfo (fun x y => y ∈ x.allRemotes) where
  getElem? x y := GetElem?.getElem? x.allRemotes y

private def AllRemotes.structBeq (x y : AllRemotes) : Bool :=
  let ⟨x⟩ := x
  let ⟨y⟩ := y
  x.size == y.size &&
  x.fold (init := true) fun soFar k v =>
    soFar && y[k]?.isEqSome v

private unsafe def AllRemotes.fastBeq (x y : AllRemotes) : Bool :=
  if ptrEq x y then true
  else
    x.allRemotes.size == y.allRemotes.size &&
    x.allRemotes.fold (init := true) fun soFar k v =>
      soFar && y.allRemotes[k]?.isEqSome v

/--
Boolean equality of full remote document information.

In compiled code, this uses pointer equality tests first, because these values are not expected to
change during the traversal pass.
-/
@[implemented_by AllRemotes.fastBeq]
public def AllRemotes.beq (x y : AllRemotes) : Bool := AllRemotes.structBeq x y

/--
Returns an array of name-remote info pairs, in some order.
-/
public def AllRemotes.toArray (all : AllRemotes) : Array (String × RemoteInfo) :=
  all.allRemotes.toArray

public instance : BEq AllRemotes where
  beq := private AllRemotes.beq

/--
Updates the remote Verso data, fetching according to the configuration.

{name}`manual` should be {lean}`true` when a user is explicitly asking for a sync, not as part of something like
executing a document renderer.
-/
public def updateRemotes (manual : Bool) (configFile : Option System.FilePath) (logVerbose : String → IO Unit) : IO AllRemotes := do
  let project ← findProject "."
  logVerbose s!"Loading project config. Project is '{project}'."
  if let some f := configFile then
    logVerbose s!"Config override is {f}."
  let config ←
    if (← hasConfig project configFile) then
      try
        getConfig project configFile
      catch e =>
        logVerbose s!"Didn't load remote data config. No remote data to be used. Error: {e}"
        return {}
    else
      logVerbose s!"No remote data configuration specified, and the default file {defaultConfigFile "."} does not exist."
      return {}

  logVerbose s!"Creating remote data cache directory {config.outputDir}"
  IO.FS.createDirAll config.outputDir
  let manifestPath := config.outputDir / "verso-xref-manifest.json"
  let xrefsPath := config.outputDir / "verso-xref.json"
  let mut values : HashMap String RemoteInfo := {}
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
        if let some remote := config.sources[k]? then
          xs.insert k <$> IO.ofExcept (fromXrefJson remote.root v)
        else pure xs
    catch | _ => pure {}
  for (name, {root, shortName, longName, updateFrequency, sources}) in config.sources do
    let mut found : Option (NameMap RefDomain) := none
    let lastUpdated := oldManifest.metadata[name]? |>.map (·.lastUpdated)
    if let some prior := lastUpdated then
      match updateFrequency with
      | .always => pure ()
      | .days d =>
        if compare (prior + d) (← Std.Time.PlainDateTime.now) |>.isGE then
          found := oldXrefs[name]?
          if let some domains := found then
            logVerbose s!"Used saved xref database for {name}, next update at {prior + d |>.toDateTimeString}"
            values := values.insert name { root, shortName, longName, domains }
            continue
      | .manual =>
        -- If this is an automatic update, attempt to use the saved value
        unless manual do
          found := oldXrefs[name]?
          if let some domains := found then
            logVerbose s!"Used saved xref database for {name}, which is to be manually synchronized"
            values := values.insert name { root, shortName, longName, domains }
            continue

    let sources := if sources.isEmpty then [.default] else sources

    let mut errors := #[]
    for s in sources do
      try
        match s with
        | .default =>
          let out ← fetchRemote project root (root ++ "/" ++ "xref.json")
          found := some out
          break
        | .localOverride f =>
          let out ← fetchFile project root f
          found := some out
          break
        | .remoteOverride url =>
          let out ← fetchRemote project root url
          found := some out
          break
      catch
        | e =>
          errors := errors.push e
    if let some domains := found then
      values := values.insert name {root, shortName, longName, domains}
      metadata := metadata.insert name { lastUpdated := (← Std.Time.PlainDateTime.now) }
    else throw <| IO.userError s!"No source found for {name}. Errors encountered:{String.join <| errors.toList.map (s!"\n * {·}")}"

  let manifest : Manifest := {config with metadata}
  logVerbose s!"Saving manifest to {manifestPath}"
  IO.FS.writeFile manifestPath (manifest.toJson.render.pretty 78)
  let valuesJson : Json := .mkObj <| values.toList.map fun (k, v) =>
    (k, .mkObj <| v.domains.toList.map fun ⟨d, o⟩ => (d.toString, o.toJson))
  IO.FS.writeFile xrefsPath (valuesJson.render.pretty 78)
  return ⟨values⟩
