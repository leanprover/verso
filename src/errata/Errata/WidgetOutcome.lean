/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
A single test's outcome as the run-test widget displays it: its output, the tree of named results,
and the verdict.

The `errata-run-one` executable builds these values and writes them as JSON. The widget's server
decodes them and passes them to the widget.
-/
module

public import Errata.Result
public import Lean.Data.Json
public import Lean.Data.Lsp.Utf16
import Std.Time

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata.Widget.Runner

open Lean in
/--
The field {name}`key` of the JSON object {name}`j`, or {name}`default` when the object has no such
field.
-/
def getObjValAsD [FromJson α] (j : Json) (key : String) (default : α) :
    Except String α := do
  let fields ← j.getObj?
  match fields.get? key with
  | some v => fromJson? v |>.mapError (s!"{key}: " ++ ·)
  | none => pure default

/-- The current wall-clock time in milliseconds since the Unix epoch. -/
def nowMs : IO Nat :=
  return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.toInt.toNat

/-- An output stream that a test can write to. -/
inductive OutputChunk.Stream where
  /-- Standard output. -/
  | stdout
  /-- Standard error. -/
  | stderr
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq, BEq

/-- A run of captured output from a single stream, used to render output with the streams distinct. -/
structure OutputChunk where
  /-- The stream the text was written to. -/
  stream : OutputChunk.Stream
  /-- The text written to that stream. -/
  text : String
  /-- When the chunk was received, in milliseconds since the Unix epoch; set by the runner. -/
  time : Nat := 0
  /--
  The identifier of the named result that wrote the chunk. {lean}`0` refers to the test itself,
  outside of any named result, while named results are assigned unique identifiers by the runner.
  -/
  result : Nat := 0
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq

/-- The chunk for a single captured output fragment, tagged by its stream. -/
def OutputChunk.ofOutput : Output → OutputChunk
  | .stdout s => { stream := .stdout, text := s }
  | .stderr s => { stream := .stderr, text := s }

/--
The verdict of one result, as the InfoView widget shows it: {name}`Errata.Status` without its
message and detail, which are separate fields of the result.
-/
inductive ResultNode.Status where
  /-- The result and everything below it passed. -/
  | passed
  /-- The result failed a check, or something below it did. -/
  | failed
  /-- An error escaped the result, so it reached no verdict of its own. -/
  | error
  /--
  The result failed within an {name (scope := "Errata.TestM")}`expectFail`, so the test's results
  omit it.
  -/
  | expectedFailure
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq, BEq

/--
The source location of a failed check, with all information needed for an InfoView widget.
-/
structure ResultNode.Source where
  /-- The document that contains the check. -/
  uri : String
  /-- The line the check starts on, counted from zero. -/
  startLine : Nat
  /-- The column the check starts at, counted from zero. -/
  startColumn : Nat
  /-- The line the check ends on, counted from zero. -/
  endLine : Nat
  /-- The column the check ends at, counted from zero. -/
  endColumn : Nat
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited, DecidableEq

/--
A source span, for an editor. Lean counts lines from one and the editor's protocol counts them from
zero.
-/
def ResultNode.Source.ofLocation (l : Location) : ResultNode.Source where
  uri := System.Uri.pathToUri l.file
  startLine := l.startPos.line - 1
  startColumn := l.startPos.column
  endLine := l.endPos.line - 1
  endColumn := l.endPos.column

/--
The span with its columns counted in UTF-16 code units, as the editor's protocol counts them. Lean
counts columns in codepoints, and the document's lines give the width of each codepoint.
{name}`linesOf` gives the lines of a file, or {lean}`none` when the file is unreadable, in which
case the span stays as it is.
-/
def ResultNode.Source.withUtf16Columns (linesOf : System.FilePath → IO (Option (Array String)))
    (s : ResultNode.Source) : IO ResultNode.Source := do
  let some path := System.Uri.fileUriToPath? s.uri
    | return s
  let some lines ← linesOf path
    | return s
  let column (line codepoints : Nat) : Nat :=
    match lines[line]? with
    | some text => Lean.String.codepointPosToUtf16Pos text codepoints
    | none => codepoints
  return { s with
    startColumn := column s.startLine s.startColumn
    endColumn := column s.endLine s.endColumn
  }

/--
One result of a run, as the InfoView widget shows it: the test's own, identified by {lit}`0`, or a
named result below it. Its output and its duration cover only its own code. The output from and
durations of named results below it are attributed to these more specific results.
-/
structure ResultNode where
  /-- The result's identifier within its run. -/
  id : Nat
  /-- The result that contains this one. -/
  parent : Nat
  /-- The name the result was given; empty for the test's own. -/
  name : String
  /-- The verdict, once the result has one. Absent while it is still running. -/
  status? : Option ResultNode.Status := none
  /-- How long the result's own code took, in milliseconds. -/
  durationMs : Nat := 0
  /-- The failure or error message, for a result that failed or erred. -/
  message? : Option String := none
  /-- Supporting detail for a failure, such as a diff or counterexample. -/
  detail? : Option String := none
  /-- Where the check that failed is, when it is known. -/
  location? : Option ResultNode.Source := none
  /-- What the result's own code wrote, in order, with each chunk tagged by its stream. -/
  output : Array OutputChunk := #[]
deriving Lean.FromJson, Lean.ToJson, Repr, Inhabited

/-- The identifier of the test's own result, which contains the named results of a run. -/
def ResultNode.root : Nat := 0

open Lean in
/-- An option passed to a test: a name and its value, which is empty for a flag. -/
structure TestOption where
  /-- The option's name, without the leading {lit}`--`. -/
  name : String
  /-- The option's value. -/
  value : String
deriving FromJson, ToJson, Repr, Inhabited

/-- The outcome of running a single test, in a form the InfoView widget renders. -/
structure RunOutcome where
  /-- The overall verdict, the most severe among the run's results. -/
  status : ResultNode.Status
  /-- How long the run took, in milliseconds. -/
  durationMs : Nat
  /-- The failure or error message, for a test that failed or erred. -/
  message? : Option String := none
  /-- Supporting detail for a failure, such as a diff or counterexample. -/
  detail? : Option String := none
  /-- Where the check that failed is, when it is known. -/
  location? : Option ResultNode.Source := none
  /--
  The run's results: the test's own, which leads, and one for each named result below it, each with
  the output its own code wrote. A result is followed by those recorded inside it.
  -/
  results : Array ResultNode := #[]
  /-- The test's docstring, rendered as Markdown, when it has one. -/
  description? : Option String := none
  /--
  The seed for property tests that the run used, so a failure can be run again with it. It is a
  string of decimal digits, which JavaScript reads exactly at any size. Present once the test itself
  has run.
  -/
  seed? : Option String := none
  /--
  The options that the run passed to the test, in the order they were given, so the run can
  be repeated with them.
  -/
  options : Array TestOption := #[]
  /--
  The names of the options that the run was given and the test never read, in alphabetical
  order.
  -/
  unreadOptions : Array String := #[]
deriving Repr, Inhabited

instance : Lean.ToJson RunOutcome where
  toJson o := Lean.Json.mkObj <|
    [("status", Lean.toJson o.status), ("durationMs", Lean.toJson o.durationMs)] ++
    Lean.Json.opt "message" o.message? ++
    Lean.Json.opt "detail" o.detail? ++
    Lean.Json.opt "location" o.location? ++
    [("results", Lean.toJson o.results)] ++
    Lean.Json.opt "description" o.description? ++
    Lean.Json.opt "seed" o.seed? ++
    [("options", Lean.toJson o.options), ("unreadOptions", Lean.toJson o.unreadOptions)]

/-- A field that is missing takes its default. -/
instance : Lean.FromJson RunOutcome where
  fromJson? j := do
    return {
      status := ← j.getObjValAs? _ "status"
      durationMs := ← j.getObjValAs? _ "durationMs"
      message? := ← Lean.fromJson? (j.getObjValD "message")
      detail? := ← Lean.fromJson? (j.getObjValD "detail")
      location? := ← Lean.fromJson? (j.getObjValD "location")
      results := ← getObjValAsD j "results" #[]
      description? := ← Lean.fromJson? (j.getObjValD "description")
      seed? := ← Lean.fromJson? (j.getObjValD "seed")
      options := ← getObjValAsD j "options" #[]
      unreadOptions := ← getObjValAsD j "unreadOptions" #[]
    }

/-- The test's own result, which contains the named results of the run. -/
def RunOutcome.root? (o : RunOutcome) : Option ResultNode :=
  o.results.find? (·.id == ResultNode.root)

/-- Everything the run wrote, its results in the order they ran. -/
def RunOutcome.allOutput (o : RunOutcome) : Array OutputChunk :=
  o.results.foldl (fun acc node => acc ++ node.output) #[]

/--
The result with the columns of its location counted in UTF-16 code units, with the lines of files
given by {Lean.Doc.name}`linesOf`.
-/
def ResultNode.withUtf16Columns (linesOf : System.FilePath → IO (Option (Array String)))
    (node : ResultNode) : IO ResultNode := do
  return { node with location? := ← node.location?.mapM (·.withUtf16Columns linesOf) }

/--
The outcome with the columns of every location in it counted in UTF-16 code units, with the lines of
files given by {name}`linesOf`.
-/
def RunOutcome.withUtf16Columns (linesOf : System.FilePath → IO (Option (Array String)))
    (outcome : RunOutcome) : IO RunOutcome := do
  return { outcome with
    location? := ← outcome.location?.mapM (·.withUtf16Columns linesOf)
    results := ← outcome.results.mapM (·.withUtf16Columns linesOf)
  }
