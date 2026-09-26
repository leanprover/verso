/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The elaborated configuration file, `.lake/errata/config.json`, as `errata-config` writes it: the
profiles with inheritance applied, each duration in milliseconds, each filter with its position, and
each setting that needs a Lake target as that target's name and position. The runner reads the
profiles, and the driver reads the targets and the added test executables.
-/
module

public import ErrataConfig.Basic

public section

set_option linter.missingDocs true
set_option doc.verso true

open Lean (Json ToJson)

namespace ErrataConfig

/-- The version of the elaborated file's format. -/
def formatVersion : Nat := 1

/-- A field that is present only when the value is. -/
def optField [ToJson α] (key : String) : Option α → List (String × Json)
  | some v => [(key, Lean.toJson v)]
  | none => []

/-- A filter's text and position in the configuration file at {name}`path`. -/
def FilterString.toJson (path : String) (f : FilterString) : Json :=
  Json.mkObj <| [("text", Json.str f.text), ("file", Json.str path),
    ("line", Lean.toJson f.line), ("col", Lean.toJson f.col)] ++
    optField "positions" f.positions?

/-- Settings as an object: each value a string, or an object that names the target it needs. -/
def settingsToJson (s : Array (String × SettingValue)) : Json :=
  Json.mkObj <| s.toList.map fun (k, v) =>
    match v with
    | .value s => (k, Json.str s)
    | .needs tgt line col =>
      (k, Json.mkObj
        [("needs", Json.str tgt), ("line", Lean.toJson line), ("col", Lean.toJson col)])

/-- An override of the configuration file at {name}`path` as an object. -/
def Override.toJson (path : String) (o : Override) : Json :=
  Json.mkObj <|
    [("filter", o.filter.toJson path)] ++ optField "timeout-ms" o.timeoutMs? ++
    optField "grace-period-ms" o.gracePeriodMs? ++
    optField "slow-after-ms" o.slowAfterMs? ++ optField "update-golden" o.updateGolden? ++
    [("settings", settingsToJson o.settings)]

/-- A profile of the configuration file at {lit}`path` as an object. -/
def Profile.toJson (path : String) (p : Profile) : Json :=
  Json.mkObj <|
    optField "timeout-ms" p.timeoutMs? ++ optField "fixture-timeout-ms" p.fixtureTimeoutMs? ++
    optField "grace-period-ms" p.gracePeriodMs? ++ optField "slow-after-ms" p.slowAfterMs? ++
    optField "jobs" p.jobs? ++ optField "order" p.order? ++
    optField "update-golden" p.updateGolden? ++
    [("settings", settingsToJson p.settings),
      ("override", Json.arr (p.overrides.map (·.toJson path)))] ++
    (match p.defaultFilter? with | some f => [("default-filter", f.toJson path)] | none => []) ++
    optField "junit" p.junit? ++ optField "json" p.json? ++ optField "markdown" p.markdown?

/-- An added test executable as an object, with its position in the file. -/
def Executable.toJson (e : Executable) : Json :=
  Json.mkObj <| [("name", Json.str e.name), ("command", Json.arr (e.command.map Json.str))] ++
    optField "cwd" e.cwd? ++ [("line", Lean.toJson e.line), ("col", Lean.toJson e.col)]

/-- The elaborated file. -/
def File.toJson (f : File) : Json :=
  Json.mkObj <| [
    ("protocol", Lean.toJson formatVersion),
    ("profiles", Json.mkObj (f.profiles.toList.map fun p => (p.name, p.toJson f.path))),
    ("executables", Json.arr (f.executables.map (·.toJson)))
  ] ++ (match f.defaultFilter? with
    | some filter => [("default-filter", filter.toJson f.path)]
    | none => [])

end ErrataConfig
