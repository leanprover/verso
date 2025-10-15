/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Json

import Std.Data.HashMap
public import Std.Time.DateTime
import Std.Time.Format

open Std
open Std.Time
open Lean

namespace Verso.Multi

public inductive XrefSource where
  | localOverride (path : System.FilePath)
  | remoteOverride (URL : String)
  /--
  Use the default location. This can be included as a fallback from local paths that don't
  necessarily exist.
  -/
  | default
deriving BEq, Repr

public def XrefSource.toJson (source : XrefSource) : Json :=
  match source with
  | .localOverride path =>
    json%{"local": $path.toString}
  | .remoteOverride url =>
    json%{"remote": $url}
  | .default =>
    "default"

public def XrefSource.fromJson? (json : Json) : Except String XrefSource :=
  match json with
  | .str "default" => pure .default
  | .obj o =>
    match o.toArray with
    | #[⟨"local", .str path⟩] => pure (.localOverride path)
    | #[⟨"remote", .str url⟩] => pure (.remoteOverride url)
    | _ =>
      throw s!"Expected a singleton object with either a 'local' or 'remote' field mapped to a string, got {json.compress}"
  | other => throw s!"Expected the string \"default\" or an object, got {other.compress}"

public inductive UpdateFrequency where
  | manual
  | days (days : Day.Offset)
deriving BEq, Repr

public def UpdateFrequency.toJson (freq : UpdateFrequency) : Json :=
  match freq with
  | .manual => .str "manual"
  | .days i => json%{"days": $i.toInt}

public def UpdateFrequency.fromJson? (freq : Json) : Except String UpdateFrequency := do
  match freq with
  | .str "manual" =>
    return .manual
  | .obj o =>
    match o.toArray with
    | #[⟨"days", i⟩] =>
      let i ← i.getInt?
      return .days (.ofInt i)
    | _ => pure ()
  | _ => pure ()
  throw <| "Expected \"manual\" or `{\"days\": i}`, got " ++ freq.compress

public instance : ToJson UpdateFrequency := ⟨UpdateFrequency.toJson⟩
public instance : FromJson UpdateFrequency := ⟨UpdateFrequency.fromJson?⟩

/--
A remote collection of documentation.
-/
public structure Remote where
  /-- The root URL for the documentation. -/
  root : String
  /--
  A short name to show users, e.g. in generated link text.
  -/
  shortName : String
  /--
  A longer name to show users, e.g. in generated link text.
  -/
  longName : String
  /--
  Sources to be attempted in order.

  `[]` is equivalent to `[.default]`.
  -/
  sources : List XrefSource
  /--
  How frequently should Verso check for updates?
  -/
  updateFrequency : UpdateFrequency
deriving BEq, Repr

public def Remote.toJson (remote : Remote) : Json :=
  let json := json%{
      "root": $remote.root,
      "shortName": $remote.shortName,
      "longName": $remote.longName,
      "updateFrequency": $remote.updateFrequency
    }
  if remote.sources.isEmpty then
    json
  else
    json.setObjVal! "sources" (.arr (remote.sources.toArray.map (·.toJson)))

public def Remote.fromJson? (remote : String) (json : Json) : Except String Remote := do
  let root ← getField? json "root"
  let shortName ← getField? json "shortName"
  let longName ← getField? json "longName"
  let sources := json.getObjValD "sources"
  let updateFrequency ← json.getObjVal? "updateFrequency"
  let updateFrequency ←
    if updateFrequency.isNull then pure .manual
    else FromJson.fromJson? updateFrequency
  if sources.isNull then
    pure {root, shortName, longName, updateFrequency, sources := []}
  else
    let .arr sources := sources
      | throw s!"Expected array of sources, got {sources.compress}"
    let sources ← sources.mapM XrefSource.fromJson?
    pure {root, shortName, longName, updateFrequency, sources := sources.toList}
where
  getField? {α} [FromJson α] (json : Json) (field : String) : Except String α := do
    let v := json.getObjValD field
    if v.isNull then throw s!"Remote '{remote}' missing field '{field}'"
    else
      try
        FromJson.fromJson? v
      catch
        | e => throw s!"Remote '{remote}' field '{field}': {e}"

public structure RemoteMeta where
  lastUpdated : PlainDateTime
deriving Repr

public structure Config where
  /-- A mapping from external source names to their root URLs. -/
  sources : HashMap String Remote
  /-- A relative directory that governs where to store Verso cross-reference data -/
  outputDir : System.FilePath
deriving Repr

public def Config.fromJson? (json : Json) : Except String Config := do
  let version ← json.getObjVal? "version"
  let version ← version.getNat? |>.mapError ("version: " ++ ·)
  if version != 0 then throw s!"Only version 0 is supported, got {version}"
  let sources ← json.getObjVal? "sources"
  let sources ← sources.getObj?
  let sources := sources.toArray.toList
  let sources ← sources.mapM fun ⟨name, remoteJson⟩ => do
    let remote ← Remote.fromJson? name remoteJson
    pure (name, remote)
  let outputDir := json.getObjValD "output"
  let outputDir ← if outputDir.isNull then pure ".verso" else FromJson.fromJson? outputDir
  pure {sources := HashMap.ofList sources, outputDir}

public structure Manifest extends Config where
  metadata : HashMap String RemoteMeta
deriving Repr

public def Manifest.toJson (manifest : Manifest) : Json :=
  let sources := Json.mkObj <|
    manifest.sources.toList.map fun (name, remote) =>
      let json := remote.toJson
      if let some {lastUpdated} := manifest.metadata[name]? then
        (name, json.setObjValAs! "updated" lastUpdated.toDateTimeString)
      else
        (name, json)
  json%{
    "version": 0,
    "sources": $sources,
    "outputDir" : $manifest.outputDir
  }

public def Manifest.fromJson? (json : Json) : Except String Manifest := do
  let config ← Config.fromJson? json
  let sourcesJson ← json.getObjVal? "sources"
  let metadata ← HashMap.ofList <$> config.sources.toList.mapM fun (k, _) => do
    let updated ← PlainDateTime.fromDateTimeString (← (← sourcesJson.getObjVal? k).getObjValAs? String "updated")
    pure (k, {lastUpdated := updated})
  pure {config with metadata}
