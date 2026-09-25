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

/-! # Terminal styles -/

/--
The styles of the human-readable output on a terminal, with the colors of nextest's reporter: green
for a pass, red for anything that did not pass, yellow for a slow test and for tests left out, bold
for counts, magenta for the executable, and blue for a test's name, whose enclosing namespaces are
cyan.
-/
inductive Style where
  /-- A pass: bold green. -/
  | pass
  /-- A failure, an error, or an inconclusive outcome: bold red. -/
  | fail
  /-- A slow test, or tests left out of the run: bold yellow. -/
  | slow
  /-- A count: bold. -/
  | count
  /-- A test executable's name: bold magenta. -/
  | exe
  /-- The enclosing namespaces of a test's name: cyan. -/
  | namespaces
  /-- The last component of a test's name: bold blue. -/
  | testName
deriving Repr, Inhabited, DecidableEq

/-- The parameters of the style's ANSI escape sequence, as nextest's color library writes them. -/
def Style.code : Style → String
  | .pass => "32;1"
  | .fail => "31;1"
  | .slow => "33;1"
  | .count => "1"
  | .exe => "35;1"
  | .namespaces => "36"
  | .testName => "34;1"

/-- Text in the style when {name}`color` is true, and the text alone otherwise. -/
def Style.paint (s : Style) (color : Bool) (text : String) : String :=
  if color && !text.isEmpty then s!"\x1b[{s.code}m{text}\x1b[0m" else text

/-- Text padded on the left with spaces to at least {name}`width` characters. -/
def padLeft (width : Nat) (text : String) : String :=
  "".pushn ' ' (width - text.length) ++ text

/--
A duration in milliseconds as nextest brackets it: seconds with three decimals, right-aligned in
eight characters.
-/
def bracketedDuration (ms : Nat) : String :=
  let frac := toString (ms % 1000)
  s!"[{padLeft 8 s!"{ms / 1000}.{"".pushn '0' (3 - frac.length)}{frac}"}s]"

/--
The name of a signal by its number, as the system's headers name it without the {lit}`SIG` prefix,
for the numbers from 1 to 15. Where macOS and Linux differ, at 7, 10, and 12, the name is the one of
the system that the runner runs on.
-/
def signalName? (signal : Nat) : Option String :=
  match signal with
  | 1 => "HUP" | 2 => "INT" | 3 => "QUIT" | 4 => "ILL" | 5 => "TRAP" | 6 => "ABRT"
  | 7 => if System.Platform.isOSX then "EMT" else "BUS"
  | 8 => "FPE" | 9 => "KILL"
  | 10 => if System.Platform.isOSX then "BUS" else "USR1"
  | 11 => "SEGV"
  | 12 => if System.Platform.isOSX then "SYS" else "USR2"
  | 13 => "PIPE" | 14 => "ALRM" | 15 => "TERM"
  | _ => none

/--
The word that the status line of a result begins with, and its style. The words are nextest's where
the outcome is one nextest has: {lit}`PASS`, {lit}`FAIL`, {lit}`TIMEOUT`, the signal's name such
as {lit}`SIGABRT`, and {lit}`XFAIL` for a test executable that could not be started. An error
verdict is {lit}`ERROR`, and the other inconclusive outcomes are {lit}`INCONCLUSIVE`. A slow test's
word is its outcome's; the line marks the slowness after the name.
-/
def statusWord (r : Result) : String × Style :=
  match r.outcome with
  | .reported .pass => ("PASS", .pass)
  | .reported (.fail _) => ("FAIL", .fail)
  | .reported (.error _) => ("ERROR", .fail)
  | .inconclusive (.timedOut ..) => ("TIMEOUT", .fail)
  | .inconclusive (.signaled s) =>
    ((signalName? s).map ("SIG" ++ ·) |>.getD s!"ABORT SIG {s}", .fail)
  | .inconclusive (.spawnFailed _) => ("XFAIL", .fail)
  | .inconclusive _ => ("INCONCLUSIVE", .fail)

/-- The width that the status word is right-aligned in, as nextest aligns it. -/
private def statusWidth : Nat := 12

/-- The indentation of the lines below a status line, which start under its duration. -/
private def detailIndent : String := "".pushn ' ' (statusWidth + 1)

/-! # The human-readable report -/

/-- The state of the human-readable reporter between tests: what to print, and the tally so far. -/
structure HumanReporter where
  /-- How much to print. -/
  verbosity : Verbosity
  /-- Whether the lines are colored for a terminal. -/
  color : Bool := false
  /-- The counts of the results reported so far. -/
  tally : Tally := {}
  /-- The executable of the test whose own line was printed last. -/
  lastExe? : Option String := none
  /-- The path of the test whose own line was printed last. -/
  lastPath : Array String := #[]
deriving Repr, Inhabited

/-- How many results of one test are printed at {name}`Verbosity.quiet` before the rest are counted. -/
private def truncationCap : Nat := 50

/--
A test's name in its styles. When the name ends with the last component of its path, the part
before that component is in the style of namespaces and the component is in the style of names;
otherwise the whole name is in the style of names.
-/
def styleTestName (color : Bool) (name : String) (path : Array String) : String :=
  let last := path.back?.getD name
  if !last.isEmpty && name.endsWith last then
    Style.namespaces.paint color (name.dropEnd last.length).copy ++
      Style.testName.paint color last
  else Style.testName.paint color name

/--
Components of a name joined by {lit}`.`, the last in the style of names and the others in the style
of namespaces.
-/
private def styleComponents (color : Bool) (parts : Array String) : String :=
  match parts.back? with
  | some last =>
    let front := parts.pop.foldl (fun acc p => acc ++ p ++ ".") ""
    Style.namespaces.paint color front ++ Style.testName.paint color last
  | none => ""

/-- The number of leading components that two paths share. -/
private def sharedPrefix (a b : Array String) : Nat :=
  (a.zip b).takeWhile (fun (x, y) => x == y) |>.size

/--
The lines of one result: its status line, with nextest's shape (the status word, the duration in
brackets, the executable, and then {name}`name`, the name column), then what explains an outcome
other than a pass, its docstring when shown, its captured output, and the command that reproduces
it.
-/
private def resultLines (h : HumanReporter) (r : Result) (name : String) : Array String := Id.run do
  let (word, style) := statusWord r
  let exe := if r.exe.isEmpty then "" else Style.exe.paint h.color r.exe ++ " "
  let slow := if r.slow then " " ++ Style.slow.paint h.color "[slow]" else ""
  let mut out := #[s!"{style.paint h.color (padLeft statusWidth word)} \
    {bracketedDuration r.durationMs} {exe}{name}{slow}"]
  let detail (text : String) := indentLines text.trimAsciiEnd.copy detailIndent
  match r.outcome with
  | .reported .pass => pure ()
  | .reported (.fail f) => out := out.push (detail f.message)
  | .reported (.error m) => out := out.push (detail m)
  | .inconclusive reason => out := out.push (detail reason.describe)
  if h.verbosity.showsAllDocstrings || !r.outcome.isPass then
    if let some d := r.description? then out := out.push (detail d)
  match r.outcome with
  | .reported (.fail f) =>
    if let some l := f.location? then out := out.push (detail l.text)
    if let some d := f.detail? then out := out.push (detail d)
  | .inconclusive (.verdictMismatch _ (.fail f)) =>
    out := out.push (detail s!"reported: {f.message}")
  | .inconclusive (.verdictMismatch _ (.error m)) => out := out.push (detail s!"reported: {m}")
  | _ => pure ()
  unless r.outcome.isPass do
    unless r.output.isEmpty do
      out := out.push (detail s!"output:\n{dropFinalNewline r.output.all}")
    if let some cmd := r.reproduce? then out := out.push (detail s!"reproduce: {cmd}")
  return out

/--
The summary line of the human-readable report, in nextest's shape: {lit}`Summary`, the run's
duration in brackets, and the counts of results by outcome. When {name}`skipped?` gives them, the
line ends with the number of listed tests that the filters left out, {lit}`N tests skipped`, and,
when they are not zero, the number of libraries with tests that the filters ruled out before
building, {lit}`M test libraries skipped`, and of the configuration's executables that they ruled
out, {lit}`K executables skipped`. Ruled-out libraries count only when a module of theirs that an
earlier build left on disk records a test.
-/
def HumanReporter.summary (h : HumanReporter) (elapsedMs : Nat)
    (skipped? : Option (Nat × Nat × Nat) := none) : String :=
  let t := h.tally
  let c := h.color
  let count (n : Nat) (word : String) (s : Style) :=
    s!"{Style.count.paint c (toString n)} {s.paint c word}"
  let style : Style :=
    if t.notPassed > 0 then .fail else if t.passed == 0 then .slow else .pass
  let counts := [count t.passed "passed" .pass, count t.failed "failed" .fail,
    count t.errors "errors" .fail, count t.inconclusive "inconclusive" .fail] ++
    (match skipped? with
      | some (tests, libs, exes) =>
        [count tests (if tests == 1 then "test skipped" else "tests skipped") .slow] ++
          (if libs == 0 then []
            else [count libs
              (if libs == 1 then "test library skipped" else "test libraries skipped") .slow]) ++
          (if exes == 0 then []
            else [count exes (if exes == 1 then "executable skipped" else "executables skipped")
              .slow])
      | none => [])
  s!"{style.paint c (padLeft statusWidth "Summary")} {bracketedDuration elapsedMs} \
    {", ".intercalate counts}"

/--
Reports the results of one test: the test's own result first, then its named results, each on a
status line of its own whose status word, duration, and executable stand in fixed columns.

The name column nests. When the test's own line follows one of the same executable whose path
shares leading components with the test's, it is indented by two spaces per shared component and
shows the rest of the path joined by {lit}`.`; otherwise it shows the test's full name. A named
result is indented two spaces below the name of its closest printed ancestor, the test's own line
included, and shows the rest of its path joined by {lit}` / `; with no printed ancestor, it shows
the test's full name and its path.

Failures, errors, and inconclusive results are printed at every verbosity.
{name}`Verbosity.quiet` adds passing results, printing at most a fixed number of lines per test and
summarizing the rest. {name}`Verbosity.verbose` shows all results, and
{name}`Verbosity.superVerbose` also shows every docstring.
-/
def HumanReporter.test (h : HumanReporter) (results : Array Result) :
    HumanReporter × Array String := Id.run do
  let h := { h with tally := results.foldl Tally.add h.tally }
  if results.isEmpty then return (h, #[])
  let v := h.verbosity
  -- Which results are printed: failures always, and passes when the verbosity shows them, up to the
  -- cap when it truncates.
  let mut shown : Array Result := #[]
  let mut count := 0
  let mut more := 0
  for r in results do
    if !r.outcome.isPass then
      shown := shown.push r
      count := count + 1
    else if v.showsPasses then
      if v.truncates && count ≥ truncationCap then
        more := more + 1
      else
        shown := shown.push r
        count := count + 1
  if shown.isEmpty then return (h, #[])
  let c := h.color
  let spaces (n : Nat) : String := "".pushn ' ' n
  let mut h := h
  let mut out : Array String := #[]
  -- The result paths printed so far for this test, the test's own as the empty path, each with the
  -- indentation of its name.
  let mut printed : Array (Array String × Nat) := #[]
  for r in shown do
    let mut name := ""
    let mut indent := 0
    if r.resultPath.isEmpty && r.kind matches .fixture then
      -- A fixture's phase is named in full: the fixture, then the phase, such as `prepare T`.
      h := { h with lastExe? := some r.exe, lastPath := #[] }
      let phase := " ".intercalate (r.path.extract 1 r.path.size).toList
      name := styleTestName c r.test #[] ++ " " ++ Style.testName.paint c phase
    else if r.resultPath.isEmpty then
      let path := if r.path.isEmpty then #[r.test] else r.path
      let shared :=
        if h.lastExe? == some r.exe then min (sharedPrefix path h.lastPath) (path.size - 1)
        else 0
      h := { h with lastExe? := some r.exe, lastPath := path }
      indent := 2 * shared
      name := if shared == 0 then styleTestName c r.test r.path
        else spaces indent ++ styleComponents c (path.extract shared path.size)
    else
      -- The closest printed ancestor: the longest printed proper prefix of the result's path.
      let ancestor? := printed.foldl (init := none) fun best (p, i) =>
        if p.size < r.resultPath.size && p.isPrefixOf r.resultPath &&
            (best.all fun (b, _) => b.size < p.size) then some (p, i)
        else best
      match ancestor? with
      | some (a, ai) =>
        let rest := r.resultPath.extract a.size r.resultPath.size
        indent := ai + 2
        name := spaces indent ++ " / ".intercalate (rest.toList.map (Style.testName.paint c))
      | none =>
        name := r.resultPath.foldl (init := styleTestName c r.test r.path) fun acc part =>
          acc ++ " / " ++ Style.testName.paint c part
    printed := printed.push (r.resultPath, indent)
    out := out ++ resultLines h r name
  if more > 0 then
    out := out.push s!"{detailIndent}(... and {more} more passed)"
  return (h, out)

/--
Prints a human-readable report of results that were gathered in one place, uncolored, and returns
the number of results that did not pass. The results of one test are contiguous, the test's own
first. The summary's duration is the sum of the results' durations.
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
  IO.println (h.summary (results.foldl (· + ·.durationMs) 0))
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
  /-- The run's identifier, which its test executables receive as {lit}`ERRATA_RUN_ID`. -/
  runId : String := ""
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
The JUnit {lit}`name` of a result: for a fixture entry, its path after the fixture's name, such as
{lit}`setup`, {lit}`prepare T`, or {lit}`teardown`, and otherwise the test's name and any named
result, dotted.
-/
def junitName (r : Result) : String :=
  match r.kind with
  | .fixture => " ".intercalate (r.path.extract 1 r.path.size).toList
  | .test => r.testName

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
    [("name", junitName r), ("classname", junitClassname r), ("time", time)]
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
      (match r.reproduce? with | some c => [("reproduce", Json.str c)] | none => []) ++
      (if r.settings.isEmpty then []
        else [("settings", Json.arr (r.settings.map fun (k, v) =>
          Json.mkObj [("name", Json.str k), ("value", Json.str v)]))]) ++
      (if r.slow then [("slow", Json.bool true)] else [])

/-- Decodes the settings of a result: an array of objects with a name and a value. -/
def resultSettings (j : Json) : Except String (Array (String × String)) := do
  match j.getObjVal? "settings" with
  | .error _ => return #[]
  | .ok v =>
    let items ← v.getArr?
    items.mapM fun item => do
      return (← item.getObjValAs? String "name", ← item.getObjValAs? String "value")

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
      reproduce? := ← optField j "reproduce",
      settings := ← resultSettings j,
      slow := (← optField j "slow").getD false
    }

/--
Renders the report as a JSON object: the results as an array of objects under {lit}`results`, the
run's issues under {lit}`issues`, the run's seed under {lit}`seed`, and the run's identifier under
{lit}`run_id`.
-/
def jsonReport (report : RunReport) : String :=
  (json%{ "results": $report.results, "issues": $report.issues, "seed": $report.seed,
    "run_id": $report.runId }).pretty

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
