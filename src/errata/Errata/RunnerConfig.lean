/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The configuration that the driver writes for the runner, `.lake/errata/config.json`: the test
executables to run, the profiles of `errata.toml` with their inheritance applied, and what the runner
needs to know about the workspace. It is the runner's only input besides its command line.
-/
module

public import Lean.Data.Json
public import Errata.Filter
public import Errata.Protocol

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
  /-- The command that starts the executable. The runner appends the protocol's arguments. -/
  command : Array String
  /-- The directory to start the executable in; the runner's own when absent. -/
  cwd? : Option String := none
  /-- Environment variables to set for the executable. -/
  env : Array (String × String) := #[]
deriving Repr, Inhabited, DecidableEq

/--
A filter's text, and where it came from: a position in the configuration file, which the driver
records, or the configuration itself when the file named none.
-/
structure FilterText where
  /-- The filter's text. -/
  text : String
  /-- Where the text is. -/
  source : Filter.Source := .argument "configuration"
deriving Repr, Inhabited, DecidableEq

/--
A per-test override in a profile: a filter over the inventory and the values that apply to the
tests it matches. For each value, the first override that matches a test and gives it wins.
-/
structure Override where
  /-- The tests that the override applies to. -/
  filter : FilterText
  /-- How long a test may run, in milliseconds. -/
  timeoutMs? : Option Nat := none
  /-- How long a fixture's phase may run, in milliseconds. -/
  fixtureTimeoutMs? : Option Nat := none
  /-- How long a terminated test has before it is killed, in milliseconds. -/
  gracePeriodMs? : Option Nat := none
  /-- How long a test runs before the report marks it slow, in milliseconds. -/
  slowAfterMs? : Option Nat := none
  /-- Whether golden checks rewrite their expected files. -/
  updateGolden? : Option Bool := none
  /-- Values of settings, by name. -/
  settings : Array (String × String) := #[]
deriving Repr, Inhabited, DecidableEq

/-- A profile, with the values of the profiles it inherits from already merged in. -/
structure Profile where
  /-- The profile's name. -/
  name : String
  /-- How long a test may run, in milliseconds. -/
  timeoutMs? : Option Nat := none
  /-- How long a fixture's phase may run, in milliseconds. -/
  fixtureTimeoutMs? : Option Nat := none
  /-- How long a terminated test has before it is killed, in milliseconds. -/
  gracePeriodMs? : Option Nat := none
  /-- How long a test runs before the report marks it slow, in milliseconds. -/
  slowAfterMs? : Option Nat := none
  /-- How many tests may run at once. -/
  jobs? : Option Nat := none
  /-- Whether golden checks rewrite their expected files. -/
  updateGolden? : Option Bool := none
  /-- Values of settings, by name. -/
  settings : Array (String × String) := #[]
  /-- The per-test overrides, in order, those of the profile's ancestors first. -/
  overrides : Array Override := #[]
  /-- The filter that selects the tests to run when the command line gives none. -/
  defaultFilter? : Option FilterText := none
deriving Repr, Inhabited, DecidableEq

/-- The runner's configuration. -/
structure Config where
  /-- The version of the configuration's format. -/
  protocol : Nat := configVersion
  /-- The test executables to list and run. -/
  executables : Array ExecutableConfig := #[]
  /--
  The directory of Errata's sources, which holds {lit}`harnesses/`. Test executables receive it as
  {lit}`ERRATA_DIR`.
  -/
  errataDir? : Option String := none
  /-- The driver's warnings about the run, reported as issues with the run as a whole. -/
  warnings : Array String := #[]
  /-- The command that the runner's options follow, such as {lit}`lake test -- --test-options`. -/
  invocation? : Option String := none
  /-- The profiles, by name. A configuration without a {lit}`default` profile has an empty one. -/
  profiles : Array Profile := #[]
  /--
  The filter that selects the tests to run when neither the profile nor the command line gives one.
  -/
  defaultFilter? : Option FilterText := none
  /--
  Whether the driver was given the names of libraries or executables to test, so that the run may
  have only some of the package's test executables.
  -/
  partialSelection : Bool := false
deriving Repr, Inhabited, DecidableEq

/-- The profile with the given name. The {lit}`default` profile always exists. -/
def Config.profile? (c : Config) (name : String) : Option Profile :=
  match c.profiles.find? (·.name == name) with
  | some p => some p
  | none => if name == "default" then some { name } else none

/-- The names of the profiles, {lit}`default` among them. -/
def Config.profileNames (c : Config) : Array String :=
  let names := c.profiles.map (·.name)
  if names.contains "default" then names else #["default"] ++ names

/-- An optional field of an object: {lean}`none` when absent or {lit}`null`. -/
def configField [FromJson α] (j : Json) (key : String) : Except String (Option α) :=
  match j.getObjVal? key with
  | .ok .null => pure none
  | .ok v => (some <$> FromJson.fromJson? v).mapError (s!"{key}: " ++ ·)
  | .error _ => pure none

/-- Decodes a filter's text and its position. -/
def FilterText.fromJson? (j : Json) : Except String FilterText := do
  let text ← j.getObjValAs? String "text" |>.mapError (s!"text: " ++ ·)
  let file? : Option String ← configField j "file"
  let line? : Option Nat ← configField j "line"
  let col? : Option Nat ← configField j "col"
  let positions : Array (Nat × Nat) := (← configField j "positions").getD #[]
  let source := match file?, line?, col? with
    | some f, some l, some c => .file f l c positions
    | _, _, _ => .argument "configuration"
  return { text, source }

instance : FromJson FilterText := ⟨FilterText.fromJson?⟩

instance : ToJson FilterText where
  toJson f := Json.mkObj <| [("text", Json.str f.text)] ++ match f.source with
    | .file path line col positions =>
      [("file", Json.str path), ("line", ToJson.toJson line), ("col", ToJson.toJson col)] ++
        if positions.isEmpty then [] else [("positions", ToJson.toJson positions)]
    | .argument _ => []

/-- Decodes the values of settings: an object whose values are strings. -/
def settingsOfJson (j : Json) : Except String (Array (String × String)) := do
  let obj ← j.getObj?
  obj.toArray.mapM fun (k, v) => do
    let s ← v.getStr? |>.mapError (s!"{k}: " ++ ·)
    return (k, s)

/-- The optional settings field of an object, with the key in any error. -/
def settingsField (j : Json) : Except String (Array (String × String)) :=
  match j.getObjVal? "settings" with
  | .ok .null | .error _ => pure #[]
  | .ok v => settingsOfJson v |>.mapError (s!"settings.{·}")

/-- The values of settings as an object. -/
def settingsToJson (s : Array (String × String)) : Json :=
  Json.mkObj (s.toList.map fun (k, v) => (k, Json.str v))

instance : FromJson Override where
  fromJson? j := do
    return {
      filter := ← j.getObjValAs? FilterText "filter" |>.mapError (s!"filter: " ++ ·)
      timeoutMs? := ← configField j "timeout-ms"
      fixtureTimeoutMs? := ← configField j "fixture-timeout-ms"
      gracePeriodMs? := ← configField j "grace-period-ms"
      slowAfterMs? := ← configField j "slow-after-ms"
      updateGolden? := ← configField j "update-golden"
      settings := ← settingsField j
    }

instance : ToJson Override where
  toJson o := Json.mkObj <|
    [("filter", ToJson.toJson o.filter)] ++
    Protocol.opt "timeout-ms" o.timeoutMs? ++ Protocol.opt "fixture-timeout-ms" o.fixtureTimeoutMs? ++
    Protocol.opt "grace-period-ms" o.gracePeriodMs? ++ Protocol.opt "slow-after-ms" o.slowAfterMs? ++
    Protocol.opt "update-golden" o.updateGolden? ++
    (if o.settings.isEmpty then [] else [("settings", settingsToJson o.settings)])

/-- Decodes a profile with the given name. Errors name the key within the profile. -/
def Profile.fromJson? (name : String) (j : Json) : Except String Profile := do
  let overrides : Array Json := (← configField j "override").getD #[]
  let overrides ← overrides.mapIdxM fun i o =>
    (FromJson.fromJson? o : Except String Override).mapError (s!"override[{i}].{·}")
  return {
    name
    timeoutMs? := ← configField j "timeout-ms"
    fixtureTimeoutMs? := ← configField j "fixture-timeout-ms"
    gracePeriodMs? := ← configField j "grace-period-ms"
    slowAfterMs? := ← configField j "slow-after-ms"
    jobs? := ← configField j "jobs"
    updateGolden? := ← configField j "update-golden"
    settings := ← settingsField j
    overrides
    defaultFilter? := ← configField j "default-filter"
  }

instance : ToJson Profile where
  toJson p := Json.mkObj <|
    Protocol.opt "timeout-ms" p.timeoutMs? ++ Protocol.opt "fixture-timeout-ms" p.fixtureTimeoutMs? ++
    Protocol.opt "grace-period-ms" p.gracePeriodMs? ++ Protocol.opt "slow-after-ms" p.slowAfterMs? ++
    Protocol.opt "jobs" p.jobs? ++ Protocol.opt "update-golden" p.updateGolden? ++
    (if p.settings.isEmpty then [] else [("settings", settingsToJson p.settings)]) ++
    (if p.overrides.isEmpty then [] else [("override", ToJson.toJson p.overrides)]) ++
    Protocol.opt "default-filter" p.defaultFilter?

/-- Decodes the profiles: an object from names to profiles. Errors name the profile and the key. -/
def profilesOfJson (j : Json) : Except String (Array Profile) := do
  let obj ← j.getObj?
  obj.toArray.mapM fun (name, p) => Profile.fromJson? name p |>.mapError (s!"{name}.{·}")

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
    let executables : Array Json := (← configField j "executables").getD #[]
    let executables ← executables.mapIdxM fun i e =>
      (FromJson.fromJson? e : Except String ExecutableConfig).mapError (s!"executables[{i}]: " ++ ·)
    let profiles ← match j.getObjVal? "profiles" with
      | .ok .null | .error _ => pure #[]
      | .ok p => profilesOfJson p |>.mapError (s!"profiles." ++ ·)
    return {
      protocol := ← j.getObjValAs? Nat "protocol" |>.mapError (s!"protocol: " ++ ·)
      executables
      errataDir? := ← configField j "errataDir"
      warnings := (← configField j "warnings").getD #[]
      invocation? := ← configField j "invocation"
      profiles
      defaultFilter? := ← configField j "default-filter"
      partialSelection := (← configField j "partial-selection").getD false
    }

instance : ToJson Config where
  toJson c := Json.mkObj <|
    [("protocol", ToJson.toJson c.protocol), ("executables", ToJson.toJson c.executables)] ++
    (match c.errataDir? with | some d => [("errataDir", Json.str d)] | none => []) ++
    [("warnings", ToJson.toJson c.warnings)] ++
    (match c.invocation? with | some i => [("invocation", Json.str i)] | none => []) ++
    (if c.profiles.isEmpty then []
      else [("profiles", Json.mkObj (c.profiles.toList.map fun p => (p.name, ToJson.toJson p)))]) ++
    Protocol.opt "default-filter" c.defaultFilter? ++
    (if c.partialSelection then [("partial-selection", Json.bool true)] else [])

/-- Reads a configuration file, checking that its version is the one this runner reads. -/
def Config.load (path : System.FilePath) : IO Config := do
  let text ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse text |>.mapError (s!"{path}: not JSON: " ++ ·))
  let cfg ← IO.ofExcept ((FromJson.fromJson? json : Except String Config).mapError (s!"{path}: " ++ ·))
  unless cfg.protocol == configVersion do
    throw <| .userError s!"{path}: the configuration's version is {cfg.protocol}, and this runner \
      reads version {configVersion}"
  return cfg
