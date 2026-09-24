/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The configuration that the driver writes for the runner, `.lake/errata/config.json`: the test
executables to run and what the runner needs to know about the workspace. It is the runner's only
input besides its command line.
-/
module

public import Lean.Data.Json

public section

set_option linter.missingDocs true
set_option doc.verso true

open Lean (Json ToJson FromJson)

namespace Errata.Runner

/-- The version of the configuration file's format that this runner reads. -/
def configVersion : Nat := 1

/-- A test executable, as the configuration names it. -/
structure ExecutableConfig where
  /-- The executable's name, unique in the run: a library's name for a Lean harness. -/
  name : String
  /-- The command that starts the executable, followed by the protocol's arguments. -/
  command : Array String
  /-- The directory to start the executable in; the runner's own when absent. -/
  cwd? : Option String := none
  /-- Environment variables to set for the executable. -/
  env : Array (String × String) := #[]
deriving Repr, Inhabited, DecidableEq

/-- The runner's configuration. -/
structure Config where
  /-- The version of the configuration's format. -/
  protocol : Nat := configVersion
  /-- The test executables to list and run. -/
  executables : Array ExecutableConfig := #[]
  /-- The directory of the Errata package, which test executables receive as {lit}`ERRATA_DIR`. -/
  errataDir? : Option String := none
  /-- The driver's warnings about the run, reported as issues with the run as a whole. -/
  warnings : Array String := #[]
  /-- The command that the runner's options follow, such as {lit}`lake test -- --test-options`. -/
  invocation? : Option String := none
deriving Repr, Inhabited, DecidableEq

/-- An optional field of an object: {lean}`none` when absent or {lit}`null`. -/
def configField [FromJson α] (j : Json) (key : String) : Except String (Option α) :=
  match j.getObjVal? key with
  | .ok .null => pure none
  | .ok v => (some <$> FromJson.fromJson? v).mapError (s!"{key}: " ++ ·)
  | .error _ => pure none

instance : FromJson ExecutableConfig where
  fromJson? j := do
    let envJson : Option Json ← configField j "env"
    let env ← match envJson with
      | none => pure #[]
      | some e =>
        let obj ← e.getObj?
        obj.toArray.mapM fun (k, v) => do return (k, ← v.getStr?)
    return {
      name := ← j.getObjValAs? String "name"
      command := ← j.getObjValAs? (Array String) "command"
      cwd? := ← configField j "cwd"
      env
    }

instance : ToJson ExecutableConfig where
  toJson e := Json.mkObj <|
    [("name", Json.str e.name), ("command", ToJson.toJson e.command)] ++
    (match e.cwd? with | some c => [("cwd", Json.str c)] | none => []) ++
    (if e.env.isEmpty then []
      else [("env", Json.mkObj (e.env.toList.map fun (k, v) => (k, Json.str v)))])

instance : FromJson Config where
  fromJson? j := do
    return {
      protocol := ← j.getObjValAs? Nat "protocol"
      executables := (← configField j "executables").getD #[]
      errataDir? := ← configField j "errataDir"
      warnings := (← configField j "warnings").getD #[]
      invocation? := ← configField j "invocation"
    }

instance : ToJson Config where
  toJson c := Json.mkObj <|
    [("protocol", ToJson.toJson c.protocol), ("executables", ToJson.toJson c.executables)] ++
    (match c.errataDir? with | some d => [("errataDir", Json.str d)] | none => []) ++
    [("warnings", ToJson.toJson c.warnings)] ++
    (match c.invocation? with | some i => [("invocation", Json.str i)] | none => [])

/-- Reads a configuration file, checking that its version is the one this runner reads. -/
def Config.load (path : System.FilePath) : IO Config := do
  let text ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse text |>.mapError (s!"{path}: not JSON: " ++ ·))
  let cfg ← IO.ofExcept ((FromJson.fromJson? json : Except String Config).mapError (s!"{path}: " ++ ·))
  unless cfg.protocol == configVersion do
    throw <| .userError s!"{path}: the configuration's version is {cfg.protocol}, and this runner \
      reads version {configVersion}"
  return cfg
