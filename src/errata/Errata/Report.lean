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

private def indentLines (text : String) (indent : String := "    ") : String :=
  "\n".intercalate ((text.splitOn "\n").map (fun l => indent ++ l))

/-- A source location rendered as the clickable `file:line:col` of the span's start. -/
private def locationText (l : Location) : String :=
  s!"{l.file}:{l.startPos.line}:{l.startPos.column}"

/--
Prints one result: its status line, its docstring when shown, and for a failure or error its detail
and captured output.

A named result whose parent's line was printed, {name}`parentShown`, is shown indented beneath it
and named by its last component alone. Otherwise a result is named in full, with its module and its
dotted test name.
-/
private def printResult (verbosity : Verbosity) (r : Result) (parentShown : Bool) : IO Unit := do
  let depth := if parentShown then r.resultPath.size else 0
  let lead := "".pushn ' ' (2 * depth)
  let detail := lead ++ "    "
  let name := match r.resultPath.back? with
    | some last => if parentShown then last else s!"{r.moduleTarget}  {r.testName}"
    | none => s!"{r.moduleTarget}  {r.testName}"
  let printDoc : IO Unit := do
    if r.resultPath.isEmpty && (verbosity.showsAllDocstrings || !r.status.isSuccess) then
      if let some d := r.description? then IO.println (indentLines d detail)
  let printOutput : IO Unit := do
    unless r.output.isEmpty do IO.println (indentLines s!"output:\n{r.output.all}" detail)
  match r.status with
  | .pass =>
    IO.println s!"{lead}ok    {name} ({r.durationMs}ms)"
    printDoc
  | .fail f =>
    IO.println s!"{lead}FAIL  {name}: {f.message}"
    printDoc
    if let some l := f.location? then IO.println (indentLines (locationText l) detail)
    if let some d := f.detail? then IO.println (indentLines d detail)
    printOutput
  | .error m =>
    IO.println s!"{lead}ERROR {name}: {m}"
    printDoc
    printOutput

/--
Prints the truncation summary for a test whose results were capped, given the number of passes that
were suppressed and the nesting depth of the last of them, so the summary lines up with its rows.
Only passing test results are ever suppressed; failures and errors are always printed.
-/
private def printSuppressed (suppressed depth : Nat) : IO Unit := do
  if suppressed > 0 then
    IO.println s!"{"".pushn ' ' (2 * depth + 4)}(... and {suppressed} more passed)"

/--
Prints a human-readable report and returns the number of failures. Failures and errors are printed
at every verbosity. {name}`Verbosity.quiet` adds passing tests, printing at most a fixed number of
lines per test, the test's own and its named results' at every depth, and summarizing the remainder.
{name}`Verbosity.verbose` shows all resutls. {name}`Verbosity.superVerbose` also shows every test's
docstring.
-/
def humanReport (verbosity : Verbosity) (results : Array Result) : IO Nat := do
  let cap := 50
  let mut passed := 0
  let mut failed := 0
  let mut errors := 0
  let mut curKey : Option (String × String) := none
  let mut shown := 0
  let mut more := 0
  let mut moreDepth := 0
  -- The printed results that enclose the current position, outermost first.
  let mut context : Array (Array String) := #[]
  for r in results do
    match r.status with
    | .pass => passed := passed + 1
    | .fail _ => failed := failed + 1
    | .error _ => errors := errors + 1
    -- Results of one test are contiguous; truncation is per test (its data-driven sub-results).
    let key := (r.moduleTarget, r.test)
    if curKey != some key then
      printSuppressed more moreDepth
      curKey := some key
      shown := 0
      more := 0
      context := #[]
    -- Pop the printed results that are not parents of the current item.
    context := context.popWhile fun top =>
      !(top.size < r.resultPath.size && top.isPrefixOf r.resultPath)
    let parentShown :=
      if let some top := context.back? then top.size + 1 == r.resultPath.size else false
    let print : IO Unit := printResult verbosity r parentShown
    match r.status with
    | .fail _ | .error _ =>
      print
      context := context.push r.resultPath
      shown := shown + 1
    | .pass =>
      if verbosity.showsPasses then
        if verbosity.truncates && shown ≥ cap then
          more := more + 1
          moreDepth := r.resultPath.size
        else
          print
          context := context.push r.resultPath
          shown := shown + 1
  printSuppressed more moreDepth
  IO.println s!"{passed} passed, {failed} failed, {errors} errors"
  return failed + errors

/--
Replaces the forbidden characters in XML 1.0 with {lit}`U+FFFD`, the canonical replacement
character, so the report shows where a character was lost. These characters are forbidden even when
escaped.

The forbidden characters are:
 * those below {lit}`U+0020` other than tab, newline, and carriage return
 * the noncharacters {lit}`U+FFFE` and {lit}`U+FFFF`.
-/
private def replaceXmlForbidden (s : String) : String :=
  s.map fun
    | c@'\t' | c@'\n' | c@'\r' => c
    | '\uFFFE' | '\uFFFF' => replacement
    | c => if c.toNat < 0x20 then replacement else c
where
  replacement := '\uFFFD'

/--
Escapes text for XML and replaces the characters that are forbidden in XML 1.0, so a captured ANSI
escape or {lit}`NUL` byte in a message or output fragment cannot make the report malformed.
-/
private def xmlEscape (s : String) : String :=
  replaceXmlForbidden <|
    s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;" |>.replace "\"" "&quot;"

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
      endPos := ⟨← j.getObjValAs? Nat "endLine", ← j.getObjValAs? Nat "endColumn"⟩
    }

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

/-- The suite a result belongs to: its package-qualified module. -/
private def suiteOf (r : Result) : String :=
  r.moduleTarget

/-- The case name of a result: the test name below the module. -/
private def caseOf (r : Result) : String :=
  r.testName

private def countWhere (results : Array Result) (p : Status → Bool) : Nat :=
  results.countP (p ·.status)

/-- Groups results by their package-qualified module in a single pass, keeping first-seen order. -/
private def byModule (results : Array Result) : Array (String × Array Result) := Id.run do
  let mut order : Array String := #[]
  let mut groups : Std.HashMap String (Array Result) := {}
  for r in results do
    let s := suiteOf r
    if !groups.contains s then order := order.push s
    groups := groups.alter s fun cur => some ((cur.getD #[]).push r)
  return order.map fun s => (s, groups.getD s #[])

/-- Renders attributes, with their values escaped, for inclusion in an opening tag. -/
private def xmlAttrs (attrs : List (String × String)) : String :=
  String.join <| attrs.map fun (name, value) => s!" {name}=\"{xmlEscape value}\""

/-- An element whose content is text, on one line at the given indentation. -/
private def xmlText (indent tag : String) (attrs : List (String × String)) (text : String := "") :
    String :=
  s!"{indent}<{tag}{xmlAttrs attrs}>{xmlEscape text}</{tag}>"

/--
An element whose content is other elements, each already rendered on its own line at a deeper
indentation. An element with no content opens and closes on one line.
-/
private def xmlElements (indent tag : String) (attrs : List (String × String))
    (children : Array String) : String :=
  if children.isEmpty then s!"{indent}<{tag}{xmlAttrs attrs}></{tag}>"
  else s!"{indent}<{tag}{xmlAttrs attrs}>\n{"\n".intercalate children.toList}\n{indent}</{tag}>"

/--
A JUnit test case: the verdict element for a failure or error, then the captured output of each
stream that has any.
-/
private def junitCase (indent suite : String) (r : Result) : String :=
  let inner := indent ++ "  "
  let verdict : Array String :=
    match r.status with
    | .pass => #[]
    | .fail f =>
      let loc := match f.location? with | some l => locationText l ++ ": " | none => ""
      #[xmlText inner "failure" [("message", loc ++ f.message)] (f.detail?.getD "")]
    | .error m => #[xmlText inner "error" [("message", m)]]
  let stream (tag text : String) : Array String :=
    if text.isEmpty then #[] else #[xmlText inner tag [] text]
  let time := toString (Float.ofNat r.durationMs / 1000.0)
  xmlElements indent "testcase" [("name", caseOf r), ("classname", suite), ("time", time)]
    (verdict ++ stream "system-out" r.output.stdout ++ stream "system-err" r.output.stderr)

/--
Renders the results as JUnit XML, grouping by the module path. A test case carries its captured
output in the {lit}`system-out` and {lit}`system-err` elements.
-/
def junitReport (results : Array Result) : String :=
  let suites := byModule results |>.map fun (_, cases) =>
    -- Every case in a group shares a package and a module, since the group is keyed by both.
    let pkg := (cases[0]?.map (·.package)).getD ""
    let suite := (cases[0]?.map (·.moduleName)).getD ""
    xmlElements "  " "testsuite"
      [("name", suite), ("package", pkg), ("tests", toString cases.size),
        ("failures", toString (countWhere cases (· matches .fail _))),
        ("errors", toString (countWhere cases (· matches .error _)))]
      (cases.map (junitCase "    " suite))
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++ xmlElements "" "testsuites" [] suites ++ "\n"

private def statusFields : Status → List (String × Json)
  | .pass => [("status", Json.str "pass")]
  | .fail f =>
    [("status", Json.str "fail"), ("message", Json.str f.message)] ++
      (match f.detail? with | some d => [("detail", Json.str d)] | none => []) ++
      (match f.location? with | some l => [("location", ToJson.toJson l)] | none => [])
  | .error m => [("status", Json.str "error"), ("message", Json.str m)]

instance : ToJson Result where
  toJson r := private
    Json.mkObj <|
      [("package", Json.str r.package), ("module", Json.str r.moduleName),
        ("test", Json.str r.test), ("resultPath", ToJson.toJson r.resultPath),
        ("durationMs", ToJson.toJson r.durationMs)] ++
      statusFields r.status ++
      (if r.output.isEmpty then [] else [("output", ToJson.toJson r.output)]) ++
      (match r.description? with | some d => [("description", Json.str d)] | none => [])

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
    | "fail" => return .fail {
        message := ← j.getObjValAs? String "message",
        detail? := ← optField j "detail",
        location? := ← optField j "location"
      }
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
      output := (← optField j "output").getD {},
      description? := ← optField j "description"
    }

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
  let icon := if failed + errors == 0 then "✅" else "❌"
  let mut out := s!"## {icon} Errata test results\n\n"
  out := out ++
    s!"**{passed}** passed · **{failed}** failed · **{errors}** errors\n\n"
  for r in results do
    let render (mark message : String) (detail? : Option String) : String := Id.run do
      let mut s := s!"<details open><summary>{mark} <code>{xmlEscape r.moduleTarget}</code> \
        {xmlEscape r.testName}: {xmlEscape message}</summary>\n\n"
      if let some d := r.description? then s := s ++ s!"{d}\n\n"
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
  out := out ++ "| Module | ✅ | ❌ | 💥 |\n| :-- | --: | --: | --: |\n"
  for (m, cs) in byModule results do
    out := out ++ s!"| {m} | {countWhere cs (· matches .pass)} | {countWhere cs (· matches .fail _)} \
      | {countWhere cs (· matches .error _)} |\n"
  return out ++ "\n</details>\n"
