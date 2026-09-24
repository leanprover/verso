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

/-- Text without its last newline, if it ends with one, for printing as lines. -/
private def dropFinalNewline (s : String) : String :=
  if s.endsWith "\n" then (s.dropEnd 1).copy else s

/-- A source location rendered as the clickable {lit}`file:line:col` of the span's start. -/
def Location.text (l : Location) : String :=
  s!"{l.file}:{l.startPos.line}:{l.startPos.column}"

/-- Counts of results by category. -/
structure Tally where
  /-- Results that passed. -/
  passed : Nat := 0
  /-- Results that failed an assertion. -/
  failed : Nat := 0
  /-- Results whose verdict is an error. -/
  errors : Nat := 0
  /-- Results that are inconclusive. -/
  inconclusive : Nat := 0
deriving Repr, Inhabited, DecidableEq

/-- Counts one more result. -/
def Tally.add (t : Tally) (r : Result) : Tally :=
  match r.outcome with
  | .reported .pass => { t with passed := t.passed + 1 }
  | .reported (.fail _) => { t with failed := t.failed + 1 }
  | .reported (.error _) => { t with errors := t.errors + 1 }
  | .inconclusive _ => { t with inconclusive := t.inconclusive + 1 }

/-- The counts of an array of results. -/
def Tally.of (results : Array Result) : Tally := results.foldl Tally.add {}

/-- The number of results that did not pass. -/
def Tally.notPassed (t : Tally) : Nat := t.failed + t.errors + t.inconclusive

/-- The summary line of the human-readable report. -/
def Tally.summary (t : Tally) : String :=
  s!"{t.passed} passed, {t.failed} failed, {t.errors} errors, {t.inconclusive} inconclusive"

/--
The state of the human-readable reporter between tests: the verbosity, the executable and the
levels of the path last printed, so that the next test's lines nest under them, and the tally so far.
-/
structure HumanReporter where
  /-- How much to print. -/
  verbosity : Verbosity
  /-- The executable whose heading was printed last. -/
  exe? : Option String := none
  /-- The levels of the path printed last, below the executable. -/
  levels : Array String := #[]
  /-- The counts of the results reported so far. -/
  tally : Tally := {}
deriving Repr, Inhabited

/-- How many results of one test are printed at {name}`Verbosity.quiet` before the rest are counted. -/
private def truncationCap : Nat := 50

/-- The label of a result's status on its line. -/
private def statusTag : Outcome → String
  | .reported .pass => "ok   "
  | .reported (.fail _) => "FAIL "
  | .reported (.error _) => "ERROR"
  | .inconclusive _ => "INCONCLUSIVE"

/--
The lines of one result: its status line, its docstring when shown, and for anything but a pass,
what explains it, its captured output, and the command that reproduces it. {name}`lead` is the
indentation of the status line, and {name}`label` is the name printed on it.
-/
private def resultLines (verbosity : Verbosity) (r : Result) (lead label : String) :
    Array String := Id.run do
  let detail := lead ++ "    "
  let mut out := #[]
  let headline := match r.outcome with
    | .reported .pass => s!"{lead}{statusTag r.outcome} {label} ({r.durationMs}ms)"
    | .reported (.fail f) => s!"{lead}{statusTag r.outcome} {label}: {f.message}"
    | .reported (.error m) => s!"{lead}{statusTag r.outcome} {label}: {m}"
    | .inconclusive reason => s!"{lead}{statusTag r.outcome} {label}: {reason.describe}"
  out := out.push headline
  if verbosity.showsAllDocstrings || !r.outcome.isPass then
    if let some d := r.description? then out := out.push (indentLines d detail)
  match r.outcome with
  | .reported .pass => pure ()
  | .reported (.fail f) =>
    if let some l := f.location? then out := out.push (indentLines l.text detail)
    if let some d := f.detail? then out := out.push (indentLines d detail)
  | .inconclusive (.verdictMismatch _ (.fail f)) =>
    out := out.push (indentLines s!"reported: {f.message}" detail)
  | .inconclusive (.verdictMismatch _ (.error m)) =>
    out := out.push (indentLines s!"reported: {m}" detail)
  | _ => pure ()
  unless r.outcome.isPass do
    unless r.output.isEmpty do
      out := out.push (indentLines s!"output:\n{dropFinalNewline r.output.all}" detail)
    if let some cmd := r.reproduce? then out := out.push (indentLines s!"reproduce: {cmd}" detail)
  return out

/--
Reports the results of one test: the test's own result first, then its named results. The lines are
nested below the test executable and the levels of the test's path, which are printed when they
differ from the previous test's. A test without a path is listed directly below its executable.

Failures, errors, and inconclusive results are printed at every verbosity.
{name}`Verbosity.quiet` adds passing results, printing at most a fixed number of lines per test and
summarizing the rest. {name}`Verbosity.verbose` shows all results, and
{name}`Verbosity.superVerbose` also shows every docstring.
-/
def HumanReporter.test (h : HumanReporter) (results : Array Result) :
    HumanReporter × Array String := Id.run do
  let h := { h with tally := results.foldl Tally.add h.tally }
  let some root := results[0]? | return (h, #[])
  let v := h.verbosity
  -- Which results are printed: failures always, and passes when the verbosity shows them, up to the
  -- cap when it truncates.
  let mut shown : Array Result := #[]
  let mut count := 0
  let mut more := 0
  let mut moreDepth := 0
  for r in results do
    if !r.outcome.isPass then
      shown := shown.push r
      count := count + 1
    else if v.showsPasses then
      if v.truncates && count ≥ truncationCap then
        more := more + 1
        moreDepth := r.resultPath.size
      else
        shown := shown.push r
        count := count + 1
  if shown.isEmpty then return (h, #[])
  let mut out : Array String := #[]
  let mut h := h
  -- The executable's heading, and the levels of the path above the test.
  let exe := root.exe
  if h.exe? != some exe then
    unless exe.isEmpty do out := out.push exe
    h := { h with exe? := some exe, levels := #[] }
  let base := if exe.isEmpty then 0 else 1
  let levels := root.path.pop
  let common := (levels.zip h.levels).takeWhile (fun (a, b) => a == b) |>.size
  for i in [common : levels.size] do
    out := out.push ("".pushn ' ' (2 * (base + i)) ++ levels[i]!)
  h := { h with levels }
  let depth := base + levels.size
  let label := root.path.back?.getD root.test
  -- The printed results that enclose the current position, outermost first.
  let mut context : Array (Array String) := #[]
  for r in shown do
    context := context.popWhile fun top =>
      !(top.size < r.resultPath.size && top.isPrefixOf r.resultPath)
    let parentShown :=
      if let some top := context.back? then top.size + 1 == r.resultPath.size else false
    let nest := if parentShown then r.resultPath.size else 0
    let lead := "".pushn ' ' (2 * (depth + nest))
    let name := match r.resultPath.back? with
      | some last => if parentShown then last else s!"{label}.{".".intercalate r.resultPath.toList}"
      | none => label
    out := out ++ resultLines v r lead name
    context := context.push r.resultPath
  if more > 0 then
    out := out.push s!"{"".pushn ' ' (2 * (depth + moreDepth) + 4)}(... and {more} more passed)"
  return (h, out)

/--
Prints a human-readable report of results that were gathered in one place, and returns the number
of results that did not pass. The results of one test are contiguous, the test's own first.
-/
def humanReport (verbosity : Verbosity) (results : Array Result) : IO Nat := do
  let mut h : HumanReporter := { verbosity }
  let mut i := 0
  while i < results.size do
    let r := results[i]!
    let mut j := i + 1
    while j < results.size && results[j]!.exe == r.exe && results[j]!.test == r.test &&
        !results[j]!.resultPath.isEmpty do
      j := j + 1
    let (h', lines) := h.test (results.extract i j)
    h := h'
    for l in lines do IO.println l
    i := j
  IO.println h.tally.summary
  return h.tally.notPassed

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
    | '￾' | '￿' => replacement
    | c => if c.toNat < 0x20 then replacement else c
where
  replacement := '�'

/--
Escapes text for XML and replaces the characters that are forbidden in XML 1.0, so a captured ANSI
escape or {lit}`NUL` byte in a message or output fragment cannot make the report malformed.
-/
def xmlEscape (s : String) : String :=
  replaceXmlForbidden <|
    s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;" |>.replace "\"" "&quot;"

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

/-- An issue with the run as a whole, raised by the driver or the runner rather than by a test. -/
structure RunReport.Issue where
  /-- Whether the issue fails the run. -/
  isError : Bool
  /-- The message. -/
  message : String
deriving Repr, Inhabited, DecidableEq

namespace RunReport.Issue

/-- The first line of an issue's message. -/
def headline (issue : Issue) : String :=
  (issue.message.splitOn "\n").headD issue.message

/-- The level an issue is reported at: {lit}`error` or {lit}`warning`. -/
def level (issue : Issue) : String :=
  if issue.isError then "error" else "warning"

end RunReport.Issue

instance : ToJson RunReport.Issue where
  toJson issue := json%{ "level": $issue.level, "message": $issue.message }

instance : FromJson RunReport.Issue where
  fromJson? j := do
    let message ← j.getObjValAs? String "message"
    match ← j.getObjValAs? String "level" with
    | "error" => return { isError := true, message }
    | "warning" => return { isError := false, message }
    | other => .error s!"unknown issue level: {other}"

/--
Everything a report renders: the results, the issues with the run as a whole, and the run's seed,
from which each test's own seed is derived.
-/
structure RunReport where
  /-- The results of every test and named result. -/
  results : Array Result
  /-- The issues with the run as a whole. -/
  issues : Array RunReport.Issue := #[]
  /-- The run's seed. -/
  seed : Nat
deriving Repr, Inhabited

/-- Whether an issue fails the run. -/
def RunReport.failsRun (report : RunReport) : Bool :=
  report.issues.any (·.isError)

/-- Whether a report counts as a successful run: every test passed and no issue is an error. -/
def RunReport.succeeded (report : RunReport) : Bool :=
  report.results.all (·.outcome.isPass) && !report.failsRun

/--
The suite under which the run's own issues are reported in formats that don't have any other slot
for them.
-/
def runSuite : String := "Test run"

/-- The note that accompanies a warning, telling how to make it fail the run. -/
private def wfailNote : String := "Run with --wfail to make warnings fail the run."

/-- Groups results by their test executable in a single pass, keeping first-seen order. -/
private def byExe (results : Array Result) : Array (String × Array Result) := Id.run do
  let mut order : Array String := #[]
  let mut groups : Std.HashMap String (Array Result) := {}
  for r in results do
    if !groups.contains r.exe then order := order.push r.exe
    groups := groups.alter r.exe fun cur => some ((cur.getD #[]).push r)
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
The JUnit {lit}`classname` of a result: a fixture's name followed by {lit}` (fixture)` for a fixture
entry, and otherwise the test's path without its last component, joined with dots, or the
executable's name when that leaves nothing.
-/
def junitClassname (r : Result) : String :=
  match r.kind with
  | .fixture => s!"{r.test} (fixture)"
  | .test =>
    let parent := r.path.pop
    if parent.isEmpty then r.exe else ".".intercalate parent.toList

/--
A JUnit test case: the verdict element for a failure, an error, or an inconclusive outcome, then the
captured output of each stream that has any.
-/
private def junitCase (indent : String) (r : Result) : String :=
  let inner := indent ++ "  "
  let verdict : Array String :=
    match r.outcome with
    | .reported .pass => #[]
    | .reported (.fail f) =>
      let loc := match f.location? with | some l => l.text ++ ": " | none => ""
      #[xmlText inner "failure" [("message", loc ++ f.message)] (f.detail?.getD "")]
    | .reported (.error m) => #[xmlText inner "error" [("message", m)]]
    | .inconclusive reason =>
      #[xmlText inner "error" [("message", s!"inconclusive: {reason.describe}"),
        ("type", reason.reasonName)] (r.reproduce?.map (s!"reproduce: {·}") |>.getD "")]
  let stream (tag text : String) : Array String :=
    if text.isEmpty then #[] else #[xmlText inner tag [] text]
  let time := toString (Float.ofNat r.durationMs / 1000.0)
  xmlElements indent "testcase"
    [("name", r.testName), ("classname", junitClassname r), ("time", time)]
    (verdict ++ stream "system-out" r.output.stdout ++ stream "system-err" r.output.stderr)

/--
A JUnit test case for an issue: an {lit}`error` element for one that fails the run, and for a
warning, the message and the way to make it fail the run in {lit}`system-err`.
-/
private def junitIssue (indent : String) (issue : RunReport.Issue) : String :=
  let inner := indent ++ "  "
  let content :=
    if issue.isError then #[xmlText inner "error" [("message", issue.headline)] issue.message]
    else #[xmlText inner "system-err" [] s!"{issue.message}\n{wfailNote}"]
  xmlElements indent "testcase" [("name", issue.headline), ("classname", runSuite)] content

/--
Renders the report as JUnit XML. The run's issues, when there are any, come first as the
{name}`runSuite` suite with one case each. The results follow, one suite per test executable: each
result becomes one {lit}`testcase` element, whose {lit}`system-out` and {lit}`system-err` elements
contain the result's captured output. A failure is a {lit}`failure` element; an error verdict and
an inconclusive outcome are {lit}`error` elements.
-/
def junitReport (report : RunReport) : String :=
  let run :=
    if report.issues.isEmpty then #[]
    else #[xmlElements "  " "testsuite"
      [("name", runSuite), ("tests", toString report.issues.size), ("failures", "0"),
        ("errors", toString (report.issues.countP (·.isError)))]
      (report.issues.map (junitIssue "    "))]
  let suites := byExe report.results |>.map fun (exe, cases) =>
    let tally := Tally.of cases
    xmlElements "  " "testsuite"
      [("name", exe), ("tests", toString cases.size), ("failures", toString tally.failed),
        ("errors", toString (tally.errors + tally.inconclusive))]
      (cases.map (junitCase "    "))
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
    xmlElements "" "testsuites" [] (run ++ suites) ++ "\n"

instance : ToJson Result where
  toJson r :=
    Json.mkObj <|
      [("exe", Json.str r.exe), ("test", Json.str r.test), ("path", ToJson.toJson r.path),
        ("kind", Json.str r.kind.name), ("resultPath", ToJson.toJson r.resultPath),
        ("durationMs", ToJson.toJson r.durationMs)] ++
      r.outcome.fields ++
      (if r.output.isEmpty then [] else [("output", ToJson.toJson r.output)]) ++
      (match r.description? with | some d => [("description", Json.str d)] | none => []) ++
      (match r.reproduce? with | some c => [("reproduce", Json.str c)] | none => [])

instance : FromJson Result where
  fromJson? j := do
    let kind ← match ← j.getObjValAs? String "kind" with
      | "test" => pure Result.Kind.test
      | "fixture" => pure .fixture
      | other => .error s!"unknown result kind: {other}"
    return {
      exe := ← j.getObjValAs? String "exe",
      test := ← j.getObjValAs? String "test",
      path := ← j.getObjValAs? (Array String) "path",
      kind,
      resultPath := ← j.getObjValAs? (Array String) "resultPath",
      durationMs := ← j.getObjValAs? Nat "durationMs",
      outcome := ← Outcome.ofFields? j,
      output := (← optField j "output").getD {},
      description? := ← optField j "description",
      reproduce? := ← optField j "reproduce"
    }

/--
Renders the report as a JSON object: the results as an array of objects under {lit}`results`, the
run's issues under {lit}`issues`, and the run's seed under {lit}`seed`.
-/
def jsonReport (report : RunReport) : String :=
  (json%{ "results": $report.results, "issues": $report.issues, "seed": $report.seed }).pretty

/-- The length of the longest run of consecutive backticks in {name}`s`. -/
private def longestBacktickRun (s : String) : Nat :=
  (s.foldl (init := (0, 0)) fun (cur, best) c =>
    if c == '`' then (cur + 1, Nat.max best (cur + 1)) else (0, best)).2

/-- Wraps {name}`body` in a fenced code block whose fence outlasts any backtick run inside it. -/
private def fencedBlock (body : String) : String :=
  let fence := String.ofList (List.replicate (Nat.max 3 (longestBacktickRun body + 1)) '`')
  s!"{fence}\n{body}\n{fence}"

/--
Renders the report as Markdown for a CI job summary: a headline tally of the four categories, each
of the run's issues and each failure, error, and inconclusive test in an open collapsible block, the
latter with its location, detail, output, and the command that reproduces it, and a table per test
executable in a closed one.
-/
def markdownReport (report : RunReport) : String := Id.run do
  let results := report.results
  let tally := Tally.of results
  let icon := if tally.notPassed == 0 && !report.failsRun then "✅" else "❌"
  let mut out := s!"## {icon} Errata test results\n\n"
  out := out ++
    s!"**{tally.passed}** passed · **{tally.failed}** failed · **{tally.errors}** errors · \
      **{tally.inconclusive}** inconclusive · seed **{report.seed}**\n\n"
  for issue in report.issues do
    let mark := if issue.isError then "💥" else "⚠️"
    out := out ++ s!"<details open><summary>{mark} {runSuite} {issue.level}: \
      {xmlEscape issue.headline}</summary>\n\n{fencedBlock issue.message}\n\n"
    unless issue.isError do out := out ++ s!"{wfailNote}\n\n"
    out := out ++ "</details>\n\n"
  for r in results do
    let render (mark message : String) (detail? : Option String) : String := Id.run do
      let mut s := s!"<details open><summary>{mark} <code>{xmlEscape r.exe}</code> \
        {xmlEscape r.testName}: {xmlEscape message}</summary>\n\n"
      if let some d := r.description? then s := s ++ s!"{d}\n\n"
      if let .reported (.fail f) := r.outcome then
        if let some l := f.location? then s := s ++ s!"`{l.text}`\n\n"
      if let some d := detail? then s := s ++ s!"{fencedBlock d}\n\n"
      unless r.output.isEmpty do
        s := s ++ s!"<details><summary>output</summary>\n\n{fencedBlock (dropFinalNewline r.output.all)}\n\n</details>\n\n"
      if let some cmd := r.reproduce? then
        s := s ++ s!"Reproduce with:\n\n{fencedBlock cmd}\n\n"
      return s ++ "</details>\n\n"
    match r.outcome with
    | .reported (.fail f) => out := out ++ render "❌" f.message f.detail?
    | .reported (.error m) => out := out ++ render "💥" m none
    | .inconclusive reason => out := out ++ render "❔" s!"inconclusive: {reason.describe}" none
    | .reported .pass => pure ()
  out := out ++ "<details><summary>Summary by test executable</summary>\n\n"
  out := out ++ "| Executable | ✅ | ❌ | 💥 | ❔ |\n| :-- | --: | --: | --: | --: |\n"
  for (exe, cs) in byExe results do
    let t := Tally.of cs
    out := out ++ s!"| {exe} | {t.passed} | {t.failed} | {t.errors} | {t.inconclusive} |\n"
  return out ++ "\n</details>\n"
