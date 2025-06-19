/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import Lean.Data.NameMap
import Std.Data.HashMap
import Std.Time.DateTime

import MultiVerso

open Lean (Json NameMap)
open Verso.Multi
open Std

structure CliConfig where
  configFile : Option System.FilePath := none
  verbose : Bool := false

def CliConfig.logVerbose (msg : String) (config : CliConfig) : IO Unit := do
  if config.verbose then IO.println msg else pure ()

inductive Command where
  | sync

def Command.name : Command → String
  | sync => "sync"

def processArgs (args : List String) : Except String (CliConfig × Command) :=
  let rec loop (config : CliConfig) (command : Option Command) : List String → Except String (CliConfig × Command)
    | "sync" :: more =>
      if let some cmd := command then
        throw s!"Unexpected subcommand 'update': subcommand is already {cmd.name}"
      else loop config (some .sync) more
    | ["--config"] => throw "Missing configuration file after '--config'"
    | "--config" :: cfg :: more =>
      loop {config with configFile := some cfg} command more
    | "-v"::more | "--verbose"::more =>
      loop { config with verbose := true } command more
    | other :: _ =>
      throw s!"Didn't understand {other}"
    | [] =>
      if let some cmd := command then pure (config, cmd)
      else throw "No subcommand specified"
  loop {} none args


def handle (cliConfig : CliConfig) : Command → IO UInt32
  | .sync => do
    discard <| updateRemotes true cliConfig.configFile cliConfig.logVerbose
    return 0


def main (args : List String) : IO UInt32 := do
  match processArgs args with
  | .error e =>
    IO.eprintln e
    return 1
  | .ok (config, cmd) =>
    handle config cmd
