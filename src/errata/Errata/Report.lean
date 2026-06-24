/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.Result
public import Lean.Data.Json

public section

open Lean (Json ToJson FromJson)

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/-- The number of failed or errored results. -/
def failureCount (results : Array Result) : Nat :=
  results.foldl (fun n r => if r.status.isSuccess then n else n + 1) 0

private def indentLines (text : String) : String :=
  "\n".intercalate ((text.splitOn "\n").map (fun l => "    " ++ l))

/-- Prints a human-readable report and returns the number of failures. -/
def humanReport (verbose : Bool) (results : Array Result) : IO Nat := do
  let mut passed := 0
  let mut failed := 0
  let mut errored := 0
  let mut skipped := 0
  for r in results do
    let name := s!"{r.moduleTarget}  {r.testName}"
    match r.status with
    | .pass =>
      passed := passed + 1
      if verbose then IO.println s!"ok    {name} ({r.durationMs}ms)"
    | .skip reason =>
      skipped := skipped + 1
      if verbose then IO.println s!"skip  {name}: {reason}"
    | .fail f =>
      failed := failed + 1
      IO.println s!"FAIL  {name}: {f.message}"
      if let some d := f.detail? then IO.println (indentLines d)
      unless r.output.isEmpty do IO.println (indentLines s!"output:\n{r.output.all}")
    | .error m =>
      errored := errored + 1
      IO.println s!"ERROR {name}: {m}"
      unless r.output.isEmpty do IO.println (indentLines s!"output:\n{r.output.all}")
  IO.println s!"{passed} passed, {failed} failed, {errored} errored, {skipped} skipped"
  return failed + errored

private def xmlEscape (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"
    |>.replace "\"" "&quot;"

/-- A source span rendered as `module:line:col-line:col`. -/
private def locationText (l : Location) : String :=
  s!"{l.moduleName}:{l.startPos.line}:{l.startPos.column}-{l.endPos.line}:{l.endPos.column}"

instance : ToJson Location where
  toJson l := json%{
    "module": $l.moduleName,
    "startLine": $l.startPos.line,
    "startColumn": $l.startPos.column,
    "endLine": $l.endPos.line,
    "endColumn": $l.endPos.column
  }

instance : FromJson Location where
  fromJson? j := do
    return {
      moduleName := ← j.getObjValAs? String "module",
      startPos := ⟨← j.getObjValAs? Nat "startLine", ← j.getObjValAs? Nat "startColumn"⟩,
      endPos := ⟨← j.getObjValAs? Nat "endLine", ← j.getObjValAs? Nat "endColumn"⟩ }

instance : ToJson Output where
  toJson
    | .stdout s => json%{ "stream": "stdout", "text": $s }
    | .stderr s => json%{ "stream": "stderr", "text": $s }

instance : FromJson Output where
  fromJson? j := do
    let text ← j.getObjValAs? String "text"
    match ← j.getObjValAs? String "stream" with
    | "stdout" => return .stdout text
    | "stderr" => return .stderr text
    | other => .error s!"unknown output stream: {other}"

instance : ToJson OutputLog where
  toJson o := ToJson.toJson o.log

instance : FromJson OutputLog where
  fromJson? j := return { log := ← FromJson.fromJson? j }

/-- The suite a result belongs to: its module. -/
private def suiteOf (r : Result) : String :=
  r.moduleName

/-- The case name of a result: the test name below the module. -/
private def caseOf (r : Result) : String :=
  r.testName

private def countWhere (results : Array Result) (p : Status → Bool) : Nat :=
  results.foldl (fun n r => if p r.status then n + 1 else n) 0

/-- Renders the results as JUnit XML, grouping by the module path. -/
def junitReport (results : Array Result) : String := Id.run do
  let suites := results.toList.map suiteOf |>.eraseDups
  let mut out := "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<testsuites>\n"
  for suite in suites do
    let cases := results.filter (fun r => suiteOf r == suite)
    let pkg := (cases[0]?.map (·.package)).getD ""
    let failures := countWhere cases (fun s => s matches .fail _)
    let errors := countWhere cases (fun s => s matches .error _)
    let skipped := countWhere cases (fun s => s matches .skip _)
    out := out ++ s!"  <testsuite name=\"{xmlEscape suite}\" package=\"{xmlEscape pkg}\" \
      tests=\"{cases.size}\" failures=\"{failures}\" errors=\"{errors}\" skipped=\"{skipped}\">\n"
    for r in cases do
      let time := toString (Float.ofNat r.durationMs / 1000.0)
      let opening := s!"    <testcase name=\"{xmlEscape (caseOf r)}\" \
        classname=\"{xmlEscape suite}\" time=\"{time}\">"
      match r.status with
      | .pass =>
        out := out ++ opening ++ "</testcase>\n"
      | .fail f =>
        let loc := match f.location? with | some l => locationText l ++ ": " | none => ""
        out := out ++ opening ++ s!"\n      <failure message=\"{xmlEscape (loc ++ f.message)}\">\
          {xmlEscape (f.detail?.getD "")}</failure>\n    </testcase>\n"
      | .error m =>
        out := out ++ opening ++ s!"\n      <error message=\"{xmlEscape m}\"></error>\n    </testcase>\n"
      | .skip reason =>
        out := out ++ opening ++ s!"\n      <skipped message=\"{xmlEscape reason}\"></skipped>\n    </testcase>\n"
    out := out ++ "  </testsuite>\n"
  out := out ++ "</testsuites>\n"
  return out

private def statusFields : Status → List (String × Json)
  | .pass => [("status", Json.str "pass")]
  | .fail f =>
    [("status", Json.str "fail"), ("message", Json.str f.message)] ++
      (match f.detail? with | some d => [("detail", Json.str d)] | none => []) ++
      (match f.location? with | some l => [("location", ToJson.toJson l)] | none => [])
  | .error m => [("status", Json.str "error"), ("message", Json.str m)]
  | .skip reason => [("status", Json.str "skip"), ("reason", Json.str reason)]

instance : ToJson Result where
  toJson r := private
    Json.mkObj <|
      [("package", Json.str r.package), ("module", Json.str r.moduleName),
        ("test", Json.str r.test), ("resultPath", ToJson.toJson r.resultPath),
        ("durationMs", ToJson.toJson r.durationMs)] ++
      statusFields r.status ++
      (if r.output.isEmpty then [] else [("output", ToJson.toJson r.output)])

/-- Decodes an optional field: absent maps to {lean}`none`. -/
private def optField [FromJson α] (j : Json) (key : String) : Except String (Option α) :=
  match j.getObjVal? key with
  | .ok v => some <$> FromJson.fromJson? v
  | .error _ => pure none

instance : FromJson Status where
  fromJson? j := private do
    match ← j.getObjValAs? String "status" with
    | "pass" => return .pass
    | "error" => return .error (← j.getObjValAs? String "message")
    | "skip" => return .skip (← j.getObjValAs? String "reason")
    | "fail" => return .fail {
        message := ← j.getObjValAs? String "message",
        detail? := ← optField j "detail",
        location? := ← optField j "location" }
    | other => .error s!"unknown status: {other}"

instance : FromJson Result where
  fromJson? j := private do
    return {
      package := ← j.getObjValAs? String "package",
      moduleName := ← j.getObjValAs? String "module",
      test := ← j.getObjValAs? String "test",
      resultPath := ← j.getObjValAs? (Array String) "resultPath",
      durationMs := ← j.getObjValAs? Nat "durationMs",
      status := ← FromJson.fromJson? j,
      output := (← optField j "output").getD {} }

/-- Renders the results as a JSON array of objects. -/
def jsonReport (results : Array Result) : String := (ToJson.toJson results).pretty
