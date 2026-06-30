/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.Result
public import Lean.Data.Json
import Std.Data.HashMap

public section

open Lean (Json ToJson FromJson)

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/-- The number of results that did not pass. -/
def failureCount (results : Array Result) : Nat :=
  results.foldl (fun n r => if r.status.isSuccess then n else n + 1) 0

private def indentLines (text : String) : String :=
  "\n".intercalate ((text.splitOn "\n").map (fun l => "    " ++ l))

/-- A source location rendered as the clickable `file:line:col` of the span's start. -/
private def locationText (l : Location) : String :=
  s!"{l.file}:{l.startPos.line}:{l.startPos.column}"

/-- Prints one result: its status line, and for a failure its detail and captured output. -/
private def printResult (r : Result) : IO Unit := do
  let name := s!"{r.moduleTarget}  {r.testName}"
  match r.status with
  | .pass => IO.println s!"ok    {name} ({r.durationMs}ms)"
  | .skip reason => IO.println s!"skip  {name}: {reason}"
  | .fail f =>
    IO.println s!"FAIL  {name}: {f.message}"
    if let some l := f.location? then IO.println (indentLines (locationText l))
    if let some d := f.detail? then IO.println (indentLines d)
    unless r.output.isEmpty do IO.println (indentLines s!"output:\n{r.output.all}")
  | .error m =>
    IO.println s!"ERROR {name}: {m}"
    unless r.output.isEmpty do IO.println (indentLines s!"output:\n{r.output.all}")

/-- A running tally of results suppressed by truncation. -/
private structure Suppressed where
  passed : Nat := 0
  failed : Nat := 0
  errors : Nat := 0
  skipped : Nat := 0

/-- Counts one more suppressed result. -/
private def Suppressed.add (s : Suppressed) : Status → Suppressed
  | .pass => { s with passed := s.passed + 1 }
  | .fail _ => { s with failed := s.failed + 1 }
  | .error _ => { s with errors := s.errors + 1 }
  | .skip _ => { s with skipped := s.skipped + 1 }

/-- The number of suppressed results. -/
private def Suppressed.total (s : Suppressed) : Nat :=
  s.passed + s.failed + s.errors + s.skipped

/-- Prints the truncation summary for a test whose results were capped, if any were suppressed. -/
private def printSuppressed (s : Suppressed) : IO Unit := do
  if s.total > 0 then
    let parts := #[s!"{s.passed} more passed", s!"{s.failed} more failed"]
      ++ (if s.errors > 0 then #[s!"{s.errors} more errors"] else #[])
      ++ (if s.skipped > 0 then #[s!"{s.skipped} more skipped"] else #[])
    IO.println s!"    (... and {", ".intercalate parts.toList})"

/--
Prints a human-readable report and returns the number of failures. Verbosity 0 shows only failures
and errors; 1 also shows passes and skips but truncates each test's results after a cap, summarizing
the rest; 2 shows everything.
-/
def humanReport (verbosity : Verbosity) (results : Array Result) : IO Nat := do
  let cap := 50
  let mut passed := 0
  let mut failed := 0
  let mut errors := 0
  let mut skipped := 0
  let mut curKey : Option (String × String) := none
  let mut shown := 0
  let mut more : Suppressed := {}
  for r in results do
    match r.status with
    | .pass => passed := passed + 1
    | .fail _ => failed := failed + 1
    | .error _ => errors := errors + 1
    | .skip _ => skipped := skipped + 1
    -- Results of one test are contiguous; truncation is per test (its data-driven sub-results).
    let key := (r.moduleTarget, r.test)
    if curKey != some key then
      printSuppressed more
      curKey := some key
      shown := 0
      more := {}
    let displayable :=
      match r.status with
      | .pass | .skip _ => verbosity.showsPasses
      | .fail _ | .error _ => true
    if displayable then
      if verbosity.truncates && shown ≥ cap then
        more := more.add r.status
      else
        printResult r
        shown := shown + 1
  printSuppressed more
  IO.println s!"{passed} passed, {failed} failed, {errors} errors, {skipped} skipped"
  return failed + errors

private def xmlEscape (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"
    |>.replace "\"" "&quot;"

instance : ToJson Location where
  toJson l := json%{
    "file": $l.file,
    "startLine": $l.startPos.line,
    "startColumn": $l.startPos.column,
    "endLine": $l.endPos.line,
    "endColumn": $l.endPos.column
  }

instance : FromJson Location where
  fromJson? j := do
    return {
      file := ← j.getObjValAs? String "file",
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

/-- Groups results by their module in a single pass, keeping each module's first-seen order. -/
private def byModule (results : Array Result) : Array (String × Array Result) := Id.run do
  let mut order : Array String := #[]
  let mut groups : Std.HashMap String (Array Result) := {}
  for r in results do
    let s := suiteOf r
    if !groups.contains s then order := order.push s
    groups := groups.insert s ((groups.getD s #[]).push r)
  return order.map fun s => (s, groups.getD s #[])

/-- Renders the results as JUnit XML, grouping by the module path. -/
def junitReport (results : Array Result) : String := Id.run do
  let mut out := "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<testsuites>\n"
  for (suite, cases) in byModule results do
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

/-- The length of the longest run of consecutive backticks in {name}`s`. -/
private def longestBacktickRun (s : String) : Nat :=
  (s.foldl (init := (0, 0)) fun (cur, best) c =>
    if c == '`' then (cur + 1, Nat.max best (cur + 1)) else (0, best)).2

/-- Wraps {name}`body` in a fenced code block whose fence outlasts any backtick run inside it. -/
private def fencedBlock (body : String) : String :=
  let fence := String.ofList (List.replicate (Nat.max 3 (longestBacktickRun body + 1)) '`')
  s!"{fence}\n{body}\n{fence}"

/--
Renders the results as Markdown for a CI job summary: a headline tally, each failure and error in an
open collapsible block with its location and detail, and a per-module table in a closed one.
-/
def markdownReport (results : Array Result) : String := Id.run do
  let passed := countWhere results (· matches .pass)
  let failed := countWhere results (· matches .fail _)
  let errors := countWhere results (· matches .error _)
  let skipped := countWhere results (· matches .skip _)
  let icon := if failed + errors == 0 then "✅" else "❌"
  let mut out := s!"## {icon} Errata test results\n\n"
  out := out ++
    s!"**{passed}** passed · **{failed}** failed · **{errors}** errors · **{skipped}** skipped\n\n"
  for r in results do
    let render (mark message : String) (detail? : Option String) : String := Id.run do
      let mut s := s!"<details open><summary>{mark} <code>{xmlEscape r.moduleTarget}</code> \
        {xmlEscape r.testName}: {xmlEscape message}</summary>\n\n"
      if let .fail f := r.status then
        if let some l := f.location? then s := s ++ s!"`{locationText l}`\n\n"
      if let some d := detail? then s := s ++ s!"{fencedBlock d}\n\n"
      unless r.output.isEmpty do
        s := s ++ s!"<details><summary>output</summary>\n\n{fencedBlock r.output.all}\n\n</details>\n\n"
      return s ++ "</details>\n\n"
    match r.status with
    | .fail f => out := out ++ render "❌" f.message f.detail?
    | .error m => out := out ++ render "💥" m none
    | _ => pure ()
  out := out ++ "<details><summary>Summary by module</summary>\n\n"
  out := out ++ "| Module | ✅ | ❌ | 💥 | ⏭️ |\n| :-- | --: | --: | --: | --: |\n"
  for (m, cs) in byModule results do
    out := out ++ s!"| {m} | {countWhere cs (· matches .pass)} | {countWhere cs (· matches .fail _)} \
      | {countWhere cs (· matches .error _)} | {countWhere cs (· matches .skip _)} |\n"
  return out ++ "\n</details>\n"
