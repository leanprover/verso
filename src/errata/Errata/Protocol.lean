/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The records that a test executable writes to its list file or its result file, one JSON object per
line. Every record has a `type`, and every other field is optional. A reader skips the records of an
unknown type and the unknown fields of a record.
-/
module

public import Errata.Failure
public import Lean.Data.Json
import Std.Time

public section

set_option linter.missingDocs true
set_option doc.verso true

open Lean (Json ToJson FromJson)

namespace Errata.Protocol

/-- The protocol version that this runner and harness speak. -/
def version : Nat := 1

/-- The oldest protocol version that the runner accepts. -/
def minVersion : Nat := 1

/-- The newest protocol version that the runner accepts. -/
def maxVersion : Nat := 1

/-- The current wall-clock time in milliseconds since the Unix epoch, as records carry it. -/
def nowMs : IO Nat :=
  return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat

/-- A source span in a record: a path, one-based lines, and codepoint columns. -/
structure Span where
  /-- The file that contains the span. -/
  file? : Option String := none
  /-- The line the span starts on, counted from one. -/
  line? : Option Nat := none
  /-- The column the span starts at, in codepoints. -/
  col? : Option Nat := none
  /-- The line the span ends on. -/
  endLine? : Option Nat := none
  /-- The column the span ends at. -/
  endCol? : Option Nat := none
deriving Repr, Inhabited, DecidableEq

/-- The span of a location. -/
def Span.ofLocation (l : Location) : Span where
  file? := some l.file
  line? := some l.startPos.line
  col? := some l.startPos.column
  endLine? := some l.endPos.line
  endCol? := some l.endPos.column

/-- The location that a span describes. Missing positions are zero, and a missing end is the start. -/
def Span.toLocation (s : Span) : Location :=
  let line := s.line?.getD 0
  let col := s.col?.getD 0
  { file := s.file?.getD ""
    startPos := ⟨line, col⟩
    endPos := ⟨s.endLine?.getD line, s.endCol?.getD col⟩ }

/-- The status of a named result or a verdict. -/
inductive Status where
  /-- It passed. -/
  | pass
  /-- It failed an assertion. -/
  | fail
  /-- An error escaped it. -/
  | error
  /-- A named result failed inside an {lit}`expectFail`, which expected it to. -/
  | expectedFailure
deriving Repr, Inhabited, DecidableEq, BEq

/-- The status's name in a record. -/
def Status.name : Status → String
  | .pass => "pass"
  | .fail => "fail"
  | .error => "error"
  | .expectedFailure => "expectedFailure"

/-- The status with the given name. -/
def Status.ofName? : String → Option Status
  | "pass" => some .pass
  | "fail" => some .fail
  | "error" => some .error
  | "expectedFailure" => some .expectedFailure
  | _ => none

/-- A setting that a test depends on, as its inventory record names it. -/
structure SettingDep where
  /-- The setting's name. -/
  name : String
  /-- Whether the test runs without a value for the setting. -/
  optional : Bool := false
deriving Repr, Inhabited, DecidableEq

instance : ToJson SettingDep where
  toJson d := Json.mkObj [("name", Json.str d.name), ("optional", Json.bool d.optional)]

instance : FromJson SettingDep where
  fromJson? j := do
    let name ← j.getObjValAs? String "name"
    let optional ← match j.getObjVal? "optional" with
      | .ok v => FromJson.fromJson? v
      | .error _ => pure false
    return { name, optional }

/-- A fixture that a test uses, as its inventory record names it. -/
structure FixtureDep where
  /-- The fixture's name. -/
  name : String
  /-- Whether the test uses the fixture alone among its users; a shared use when false. -/
  exclusive : Bool := true
deriving Repr, Inhabited, DecidableEq

instance : ToJson FixtureDep where
  toJson d := Json.mkObj [("name", Json.str d.name), ("exclusive", Json.bool d.exclusive)]

instance : FromJson FixtureDep where
  fromJson? j := do
    let name ← j.getObjValAs? String "name"
    let exclusive ← match j.getObjVal? "exclusive" with
      | .ok v => FromJson.fromJson? v
      | .error _ => pure true
    return { name, exclusive }

/-- An inventory entry for a fixture. Only the name is required of a test executable. -/
structure FixtureInfo where
  /-- The fixture's name, unique within the inventory. -/
  name? : Option String := none
  /-- The fixture's description. -/
  description? : Option String := none
  /-- The settings that the fixture depends on, each mandatory or optional. -/
  settings? : Option (Array SettingDep) := none
  /-- The names of the fixtures that the fixture depends on, each declared before it. -/
  fixtures? : Option (Array String) := none
  /-- The number of hardware threads that the fixture's phases ask for; one when absent. -/
  threads? : Option Nat := none
deriving Repr, Inhabited, DecidableEq

/-- An inventory entry for a test. Only the name is required of a test executable. -/
structure TestInfo where
  /-- The test's name, unique within the inventory. -/
  name? : Option String := none
  /-- The components of the test's name, for nesting in reports. -/
  path? : Option (Array String) := none
  /-- The file that defines the test. -/
  file? : Option String := none
  /-- The line of the test's declaration, counted from one. -/
  line? : Option Nat := none
  /-- The column of the test's declaration. -/
  col? : Option Nat := none
  /-- The test's description. -/
  description? : Option String := none
  /-- {lit}`test` or {lit}`benchmark`; a test when absent. -/
  kind? : Option String := none
  /-- The test's tags. -/
  tags? : Option (Array String) := none
  /-- The settings that the test depends on, each mandatory or optional. -/
  settings? : Option (Array SettingDep) := none
  /-- The fixtures that the test uses, each exclusive or shared. -/
  fixtures? : Option (Array FixtureDep) := none
  /-- The number of hardware threads that the test asks for; one when absent. -/
  threads? : Option Nat := none
deriving Repr, Inhabited, DecidableEq

/-- A named result's report, when it starts (without a status) and when it finishes. -/
structure ResultInfo where
  /-- The result's identifier within the run; the test itself is {lit}`0`. -/
  id? : Option Nat := none
  /-- The identifier of the result that contains this one. -/
  parent? : Option Nat := none
  /-- The name the result was given. -/
  name? : Option String := none
  /-- The status, once the result has finished. -/
  status? : Option Status := none
  /-- The failure or error message. -/
  message? : Option String := none
  /-- Supporting detail, such as a diff. -/
  detail? : Option String := none
  /-- Where the check that failed is. -/
  location? : Option Span := none
  /-- How long the result's own code took, in milliseconds. -/
  durationMs? : Option Nat := none
deriving Repr, Inhabited, DecidableEq

/-- A test's own verdict, or a fixture phase's. -/
structure VerdictInfo where
  /-- The status. -/
  status? : Option Status := none
  /-- The failure or error message. -/
  message? : Option String := none
  /-- Supporting detail, such as a diff. -/
  detail? : Option String := none
  /-- Where the check that failed is. -/
  location? : Option Span := none
  /-- How long the test took, as the test executable measured it, in milliseconds. -/
  durationMs? : Option Nat := none
deriving Repr, Inhabited, DecidableEq

/-- One line of a test executable's list file or result file. -/
inductive Record where
  /-- The protocol version, the first record of every file. -/
  | protocol (version? : Option Nat)
  /-- A setting that the test executable's tests take. -/
  | setting (name? description? default? : Option String)
  /-- A fixture that the test executable's tests use. -/
  | fixture (info : FixtureInfo)
  /-- A test in the inventory. -/
  | test (info : TestInfo)
  /-- The test body has begun. -/
  | start (timeMs? : Option Nat)
  /-- Text that the test wrote, and the named result that was open when it wrote it. -/
  | output (stream? text? : Option String) (timeMs? result? : Option Nat)
  /-- A named result has started or finished. -/
  | result (info : ResultInfo)
  /-- The test's own verdict. -/
  | verdict (info : VerdictInfo)
  /-- A fixture's value, from its setup. -/
  | value (text? : Option String)
deriving Repr, Inhabited, DecidableEq

/-- A field that is present only when the value is. -/
def opt [ToJson α] (key : String) : Option α → List (String × Json)
  | some v => [(key, ToJson.toJson v)]
  | none => []

instance : ToJson Span where
  toJson s := Json.mkObj <|
    opt "file" s.file? ++ opt "line" s.line? ++ opt "col" s.col? ++ opt "endLine" s.endLine? ++
      opt "endCol" s.endCol?

instance : ToJson Status where
  toJson s := Json.str s.name

/-- The record as a JSON object. -/
def Record.toJson : Record → Json
  | .protocol v => Json.mkObj <| ("type", Json.str "protocol") :: opt "version" v
  | .setting n d dflt =>
    Json.mkObj <| ("type", Json.str "setting") :: opt "name" n ++ opt "description" d ++ opt "default" dflt
  | .fixture i =>
    Json.mkObj <| ("type", Json.str "fixture") :: opt "name" i.name? ++
      opt "description" i.description? ++ opt "settings" i.settings? ++
      opt "fixtures" i.fixtures? ++ opt "threads" i.threads?
  | .test i =>
    Json.mkObj <| ("type", Json.str "test") :: opt "name" i.name? ++ opt "path" i.path? ++
      opt "file" i.file? ++ opt "line" i.line? ++ opt "col" i.col? ++
      opt "description" i.description? ++ opt "kind" i.kind? ++ opt "tags" i.tags? ++
      opt "settings" i.settings? ++ opt "fixtures" i.fixtures? ++ opt "threads" i.threads?
  | .start t => Json.mkObj <| ("type", Json.str "start") :: opt "time_ms" t
  | .output s t time r =>
    Json.mkObj <| ("type", Json.str "output") :: opt "stream" s ++ opt "text" t ++ opt "time_ms" time ++
      opt "result" r
  | .result i =>
    Json.mkObj <| ("type", Json.str "result") :: opt "id" i.id? ++ opt "parent" i.parent? ++
      opt "name" i.name? ++ opt "status" i.status? ++ opt "message" i.message? ++
      opt "detail" i.detail? ++ opt "location" i.location? ++ opt "duration_ms" i.durationMs?
  | .verdict i =>
    Json.mkObj <| ("type", Json.str "verdict") :: opt "status" i.status? ++ opt "message" i.message? ++
      opt "detail" i.detail? ++ opt "location" i.location? ++ opt "duration_ms" i.durationMs?
  | .value t => Json.mkObj <| ("type", Json.str "value") :: opt "text" t

instance : ToJson Record where
  toJson := Record.toJson

/--
The optional field {name}`key` of {name}`j`: {lean}`none` when it is absent or {lit}`null`, and an
error naming the field when it has the wrong shape.
-/
private def field [FromJson α] (j : Json) (key : String) : Except String (Option α) :=
  match j.getObjVal? key with
  | .ok .null => pure none
  | .ok v => match FromJson.fromJson? v with
    | .ok x => pure (some x)
    | .error e => .error s!"field {key}: {e}"
  | .error _ => pure none

/-- Decodes a span, ignoring unknown fields. -/
private def decodeSpan (j : Json) : Except String Span := do
  return {
    file? := ← field j "file", line? := ← field j "line", col? := ← field j "col",
    endLine? := ← field j "endLine", endCol? := ← field j "endCol"
  }

/-- The optional span field {name}`key` of {name}`j`. -/
private def spanField (j : Json) (key : String) : Except String (Option Span) :=
  match j.getObjVal? key with
  | .ok .null => pure none
  | .ok v => some <$> decodeSpan v
  | .error _ => pure none

/-- The optional status field of {name}`j`. -/
private def statusField (j : Json) : Except String (Option Status) := do
  match ← (field j "status" : Except String (Option String)) with
  | none => pure none
  | some s => match Status.ofName? s with
    | some st => pure (some st)
    | none => .error s!"field status: unknown status {s}"

/--
Decodes one record. A record of an unknown type decodes to {lean}`none`, and unknown fields are
skipped. A value that is not an object with a string {lit}`type`, or a known field of the wrong
shape, is an error.
-/
def Record.decode? (j : Json) : Except String (Option Record) := do
  let .ok (ty : String) := j.getObjValAs? String "type"
    | .error "the record has no type"
  match ty with
  | "protocol" => return some (.protocol (← field j "version"))
  | "setting" =>
    return some (.setting (← field j "name") (← field j "description") (← field j "default"))
  | "fixture" =>
    return some (.fixture {
      name? := ← field j "name", description? := ← field j "description",
      settings? := ← field j "settings", fixtures? := ← field j "fixtures",
      threads? := ← field j "threads"
    })
  | "test" =>
    return some (.test {
      name? := ← field j "name", path? := ← field j "path", file? := ← field j "file",
      line? := ← field j "line", col? := ← field j "col",
      description? := ← field j "description", kind? := ← field j "kind",
      tags? := ← field j "tags", settings? := ← field j "settings",
      fixtures? := ← field j "fixtures", threads? := ← field j "threads"
    })
  | "start" => return some (.start (← field j "time_ms"))
  | "output" =>
    return some (.output (← field j "stream") (← field j "text") (← field j "time_ms")
      (← field j "result"))
  | "result" =>
    return some (.result {
      id? := ← field j "id", parent? := ← field j "parent", name? := ← field j "name",
      status? := ← statusField j, message? := ← field j "message", detail? := ← field j "detail",
      location? := ← spanField j "location", durationMs? := ← field j "duration_ms"
    })
  | "verdict" =>
    return some (.verdict {
      status? := ← statusField j, message? := ← field j "message", detail? := ← field j "detail",
      location? := ← spanField j "location", durationMs? := ← field j "duration_ms"
    })
  | "value" => return some (.value (← field j "text"))
  | _ => return none

/--
Decodes one line of a list file or a result file, as {name}`Record.decode?` does, with the parsed
JSON.
-/
def Record.parseLine (line : String) : Except String (Option (Json × Record)) := do
  let j ← Json.parse line |>.mapError (s!"not JSON: {·}")
  match ← Record.decode? j with
  | some r => return some (j, r)
  | none => return none

/-- Appends one record to a list file or a result file as a line of JSON, and flushes it. -/
def writeRecord (out : IO.FS.Handle) (r : Record) : IO Unit := do
  out.putStr (r.toJson.compress ++ "\n")
  out.flush
