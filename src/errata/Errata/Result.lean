/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.Failure
public import Errata.Outcome

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/-- How much the human-readable report prints. -/
inductive Verbosity where
  /-- Print only failures, errors, and inconclusive tests. -/
  | silent
  /-- Also print passes, truncating each test's results after a cap. -/
  | quiet
  /-- Print every result. -/
  | verbose
  /-- Print every result, and each test's docstring alongside it, not only those that fail. -/
  | superVerbose
deriving Repr, Inhabited, DecidableEq, BEq

/-- Whether passes are printed at this verbosity. -/
def Verbosity.showsPasses : Verbosity → Bool
  | .silent => false
  | .quiet | .verbose | .superVerbose => true

/--
Whether a test that produces many passing results has only the first few of them printed,
with a count of the rest. Failures and errors are always printed in full, so truncation isn't
relevant at {name}`silent` verbosity.
-/
def Verbosity.truncates : Verbosity → Bool
  | .silent => false
  | .quiet => true
  | .verbose | .superVerbose => false

/-- Whether every result's docstring is shown, not only those of failures and errors. -/
def Verbosity.showsAllDocstrings : Verbosity → Bool
  | .silent | .quiet | .verbose => false
  | .superVerbose => true

/-- A fragment of captured output, tagged by the stream it was written to. -/
inductive Output where
  /-- Text written to standard output. -/
  | stdout (text : String)
  /-- Text written to standard error. -/
  | stderr (text : String)
deriving Repr, Inhabited, DecidableEq

/-- The text of an output fragment, regardless of stream. -/
def Output.text : Output → String
  | .stdout s | .stderr s => s

/-- All captured output, concatenated in order. -/
def capturedText (output : Array Output) : String :=
  output.foldl (fun acc o => acc ++ o.text) ""

/-- Output captured from an action, in order and tagged by stream. -/
structure OutputLog where
  /-- The captured fragments, in order, tagged by stream. -/
  log : Array Output := #[]
deriving Repr, Inhabited, DecidableEq

namespace OutputLog

/-- Whether no output was captured. -/
def isEmpty (o : OutputLog) : Bool := o.log.isEmpty

/-- The text written to stdout, concatenated in order. -/
def stdout (o : OutputLog) : String :=
  o.log.foldl (fun acc out => match out with | .stdout s => acc ++ s | .stderr _ => acc) ""

/-- The text written to stderr, concatenated in order. -/
def stderr (o : OutputLog) : String :=
  o.log.foldl (fun acc out => match out with | .stderr s => acc ++ s | .stdout _ => acc) ""

/-- The text written to stdout and stderr, concatenated in order. -/
def all (o : OutputLog) : String := capturedText o.log

end OutputLog

/-- What a result is about: a test, or a phase of a fixture. -/
inductive Result.Kind where
  /-- A test or one of its named results. -/
  | test
  /-- A phase of a fixture. -/
  | fixture
deriving Repr, Inhabited, DecidableEq, BEq

/-- The name of a result's kind, as the reports write it. -/
def Result.Kind.name : Result.Kind → String
  | .test => "test"
  | .fixture => "fixture"

/--
One entry collected during a run and rendered by the reporters: a test's own result, or one of its
named results.
-/
structure Result where
  /-- The name of the test executable that ran the test. -/
  exe : String := ""
  /-- The test's name, unique within its test executable. -/
  test : String
  /-- The components of the test's name, for nesting in reports; empty when it has none. -/
  path : Array String := #[]
  /-- Whether the result is about a test or a fixture phase. -/
  kind : Result.Kind := .test
  /-- The named result below the test; empty for the test's own result. -/
  resultPath : Array String := #[]
  /-- How the test or named result ended. -/
  outcome : Outcome
  /-- How long the check took, in milliseconds. -/
  durationMs : Nat := 0
  /-- What the test wrote to stdout and stderr. -/
  output : OutputLog := {}
  /-- The test's docstring, rendered as Markdown, when it has one. -/
  description? : Option String := none
  /-- A command line that runs the test again by hand, for a test that did not pass. -/
  reproduce? : Option String := none
  /-- The settings that the test received, in the order it received them, on the test's own result. -/
  settings : Array (String × String) := #[]
  /-- Whether the test ran for longer than the configuration's {lit}`slow-after`. -/
  slow : Bool := false
deriving Repr, Inhabited, DecidableEq

/--
The result's status: its verdict, or an error for an inconclusive outcome, which counts against the
run as an error does.
-/
def Result.status (r : Result) : Status := r.outcome.toStatus

/-- Whether the result's outcome is inconclusive. -/
def Result.isInconclusive (r : Result) : Bool := r.outcome matches .inconclusive _

/--
What a test is doing, for a runner that follows it while it runs.

Both named results and {name (scope := "Errata.TestM")}`expectFail` are logged both at start and
finish.  The events of nested tests form a tree.
-/
inductive ResultEvent where
  /-- The named result at this path has started. -/
  | started (path : Array String)
  /-- The named result at this path has finished, with this outcome. -/
  | finished (result : Result)
  /-- An {name (scope := "Errata.TestM")}`expectFail` has started. -/
  | expectFailStarted
  /--
  An {name (scope := "Errata.TestM")}`expectFail` has ended. When {name}`failuresExpected` is true,
  the named results that failed within it were expected to fail, so they should be omitted from the
  test results.
  -/
  | expectFailFinished (failuresExpected : Bool)
deriving Repr, Inhabited

/-- The test's name and any named result, dotted. -/
def Result.testName (result : Result) : String :=
  if result.resultPath.isEmpty then result.test
  else result.test ++ "." ++ ".".intercalate result.resultPath.toList

/-- A failed verdict from a compile-time message mismatch, carrying its source span. -/
def TestResult.mismatch (message detail file : String)
    (startLine startCol endLine endCol : Nat) : TestResult :=
  .fail {
    message,
    detail? := some detail,
    location? := some {
      file,
      startPos := { line := startLine, column := startCol },
      endPos := { line := endLine, column := endCol }
    }
  }
