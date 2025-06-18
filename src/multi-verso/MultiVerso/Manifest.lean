/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json

import Std.Data.HashMap
import Std.Time.DateTime
import Std.Time.Format

open Std
open Std.Time
open Lean

namespace Verso.Multi

inductive XrefSource where
  | localOverride (path : System.FilePath)
  | remoteOverride (URL : String)
  /--
  Use the default location. This can be included as a fallback from local paths that don't
  necessarily exist.
  -/
  | default
deriving BEq

def XrefSource.toJson (source : XrefSource) : Json :=
  match source with
  | .localOverride path =>
    json%{"local": $path.toString}
  | .remoteOverride url =>
    json%{"remote": $url}
  | .default =>
    "default"

def XrefSource.fromJson? (json : Json) : Except String XrefSource :=
  match json with
  | .str "default" => pure .default
  | .obj o =>
    match o.toArray with
    | #[⟨"local", .str path⟩] => pure (.localOverride path)
    | #[⟨"remote", .str url⟩] => pure (.remoteOverride url)
    | _ =>
      throw s!"Expected a singleton object with either a 'local' or 'remote' field mapped to a string, got {json.compress}"
  | other => throw s!"Expected the string \"default\" or an object, got {other.compress}"

/--
A remote collection of documentation.
-/
structure Remote where
  /-- The root URL for the documentation. -/
  root : String
  /--
  Sources to be attempted in order.

  `[]` is equivalent to `[.default]`.
  -/
  sources : List XrefSource
deriving BEq

def Remote.toJson (remote : Remote) : Json :=
  if remote.sources.isEmpty then
    json%{"root": $remote.root}
  else
    json%{
      "root": $remote.root,
      "sources": $(remote.sources.map (·.toJson))
    }

def Remote.fromJson? (json : Json) : Except String Remote := do
  let root ← json.getObjValAs? String "root"
  let sources := json.getObjValD "sources"
  if sources.isNull then
    pure {root, sources := []}
  else
    let .arr sources := sources
      | throw s!"Expected array of sources, got {sources.compress}"
    let sources ← sources.mapM XrefSource.fromJson?
    pure {root, sources := sources.toList}

structure RemoteMeta where
  lastUpdated : PlainDateTime

structure Config where
  /-- A mapping from external source names to their root URLs. -/
  sources : HashMap String Remote
  /-- A relative directory that governs where to store Verso cross-reference data -/
  outputDir : System.FilePath

def Config.fromJson? (json : Json) : Except String Config := do
  let version ← json.getObjVal? "version"
  let version ← version.getNat? |>.mapError ("version: " ++ ·)
  if version != 0 then throw s!"Only version 0 is supported, got {version}"
  let sources ← json.getObjVal? "sources"
  let sources ← sources.getObj?
  let sources := sources.toArray.toList
  let sources ← sources.mapM fun ⟨name, remoteJson⟩ => do
    let remote ← Remote.fromJson? remoteJson
    pure (name, remote)
  let outputDir := json.getObjValD "output"
  let outputDir ← if outputDir.isNull then pure ".verso" else FromJson.fromJson? outputDir
  pure {sources := HashMap.ofList sources, outputDir}

structure Manifest extends Config where
  metadata : HashMap String RemoteMeta

def Manifest.toJson (manifest : Manifest) : Json :=
  let sources := Json.mkObj <|
    manifest.sources.toList.map fun (name, remote) =>
      let json := remote.toJson
      if let some {lastUpdated} := manifest.metadata[name]? then
        (name, json.setObjValAs! "updated" lastUpdated.toDateTimeString)
      else
        (name, json)
  json%{
    "version": 0,
    "sources": $sources
  }
