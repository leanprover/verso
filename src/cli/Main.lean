/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import Lean.Data.NameMap
import Std.Data.HashMap

import MultiVerso

open Lean (Json NameMap)
open Verso.Multi
open Std

structure CliConfig where
  configFile : Option System.FilePath := none

inductive Command where
  | update

def Command.name : Command → String
  | .update => "update"

def processArgs (args : List String) : Except String (CliConfig × Command) :=
  let rec loop (config : CliConfig) (command : Option Command) : List String → Except String (CliConfig × Command)
    | "update" :: more =>
      if let some cmd := command then
        throw s!"Unexpected subcommand 'update': subcommand is already {cmd.name}"
      else loop config (some .update) more
    | ["--config"] => throw "Missing configuration file after '--config'"
    | "--config" :: cfg :: more =>
      loop {config with configFile := some cfg} command more
    | other :: _ =>
      throw s!"Didn't understand {other}"
    | [] =>
      if let some cmd := command then pure (config, cmd)
      else throw "No subcommand specified"
  loop {} none args

def normPath (path : System.FilePath) : System.FilePath :=
  System.mkFilePath <| removeSpecial path.components
where
  removeSpecial xs := remove' xs.reverse |>.reverse
  remove'
    | [] => []
    | [x] => [x]
    | ".." :: _ :: xs => remove' xs
    | "." :: xs => remove' xs
    | x :: xs => x :: remove' xs


partial def findProject (path : System.FilePath) : IO System.FilePath := do
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

def getConfig (project : System.FilePath) (config : CliConfig) : IO Config := do
    let configFile : System.FilePath :=
      if let some f := config.configFile then f
      else project / "verso-sources.json"
    let configJson ← IO.FS.readFile configFile
    let configJson ← Json.parse configJson |> IO.ofExcept
    Config.fromJson? configJson |> IO.ofExcept

def fetchRemote (project : System.FilePath) (url : String) : IO (NameMap RefDomain) := do
  let json ←
    IO.Process.run {
      cmd := "curl",
      args := #[url]
      cwd := project
    }
  let json ← Json.parse json |> IO.ofExcept
  fromXrefJson json |> IO.ofExcept

def fetchFile (project : System.FilePath) (file : System.FilePath) : IO (NameMap RefDomain) := do
  let json ← IO.FS.readFile (project / file)
  let json ← Json.parse json |> IO.ofExcept
  fromXrefJson json |> IO.ofExcept

def handle (config : CliConfig) : Command → IO UInt32
  | .update => do
    let project ← findProject "."
    let config ← getConfig project config
    let mut values : HashMap String (NameMap RefDomain) := {}
    for (name, {root, sources}) in config.sources do
      let sources := if sources.isEmpty then [.default] else sources
      let mut found : Option (NameMap RefDomain) := none
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
        values := values.insert name v
      else throw <| IO.userError s!"No source found for {name}"
    dbg_trace repr values
    return 0


def main (args : List String) : IO UInt32 := do
  match processArgs args with
  | .error e =>
    IO.eprintln e
    return 1
  | .ok (config, cmd) =>
    handle config cmd
