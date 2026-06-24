/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/-- How much the human-readable report prints. -/
inductive Verbosity where
  /-- Print only failures and errors. -/
  | silent
  /-- Also print passes and skips, truncating each test's results after a cap. -/
  | quiet
  /-- Print every result. -/
  | verbose
deriving Repr, Inhabited, DecidableEq, BEq

/-- Whether passes and skips are printed at this verbosity. -/
def Verbosity.showsPasses : Verbosity → Bool
  | .silent => false
  | .quiet | .verbose => true

/-- Whether each test's results are truncated after a cap at this verbosity. -/
def Verbosity.truncates : Verbosity → Bool
  | .quiet => true
  | .silent | .verbose => false

/-- The next verbosity up, for an accumulating {lit}`-v` / {lit}`-vv`. -/
def Verbosity.increase : Verbosity → Verbosity
  | .silent => .quiet
  | .quiet | .verbose => .verbose

/-- A line and column within a source file, counting from one. -/
structure Position where
  /-- The line, counting from one. -/
  line : Nat
  /-- The column, counting from one. -/
  column : Nat
deriving Repr, Inhabited, BEq, DecidableEq

/-- A source span, used in failure messages and editor integration. -/
structure Location where
  /-- The module that contains the span, rendered as a string. -/
  moduleName : String
  /-- The start of the span. -/
  startPos : Position
  /-- The end of the span. -/
  endPos : Position
deriving Repr, Inhabited, BEq, DecidableEq

/-- A test failure, carrying the information needed to explain it. -/
structure TestFailure where
  /-- A short description of what went wrong. -/
  message : String
  /-- Supporting detail, such as a diff, a counterexample, or expected and actual values. -/
  detail? : Option String := none
  /-- The source location of the failed check, when known. -/
  location? : Option Location := none
deriving Repr, Inhabited, DecidableEq

/-- The verdict that a test body may return. -/
inductive TestResult where
  /-- The test passed. -/
  | pass
  /-- The test failed, with details. -/
  | fail (failure : TestFailure)
  /-- The test was skipped, with a reason. -/
  | skip (reason : String)
deriving Repr, Inhabited

/-- The recorded outcome of a test or a named result. -/
inductive Status where
  /-- The check passed. -/
  | pass
  /-- The check failed. -/
  | fail (failure : TestFailure)
  /-- An error escaped the check, so it could not produce a verdict. -/
  | error (message : String)
  /-- The check was skipped. -/
  | skip (reason : String)
deriving Repr, Inhabited, DecidableEq

/-- Whether a status counts as success for the exit code. -/
def Status.isSuccess : Status → Bool
  | .pass | .skip _ => true
  | .fail _ | .error _ => false

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

/-- One entry collected during a run and rendered by the reporters. -/
structure Result where
  /-- The package that defines the test. -/
  package : String
  /-- The module that defines the test, as a dotted name. -/
  moduleName : String
  /-- The test declaration's name below its module, as a dotted name. -/
  test : String
  /-- The named result below the test; empty for the test's own result. -/
  resultPath : Array String := #[]
  /-- The recorded outcome. -/
  status : Status
  /-- How long the check took, in milliseconds. -/
  durationMs : Nat := 0
  /-- What the test wrote to stdout and stderr. -/
  output : OutputLog := {}
deriving Repr, Inhabited, DecidableEq

/-- The test name below the module: the declaration and any named result, dotted. -/
def Result.testName (result : Result) : String :=
  if result.resultPath.isEmpty then result.test
  else result.test ++ "." ++ ".".intercalate result.resultPath.toList

/--
The module as a Lake target specification ({lit}`package/module`). This is the unit of execution:
passing it to {lit}`lake test` re-runs the module that produced the result.
-/
def Result.moduleTarget (result : Result) : String :=
  result.package ++ "/" ++ result.moduleName

/-- A failed verdict from a compile-time message mismatch, carrying its source span. -/
def TestResult.mismatch (message detail moduleName : String)
    (startLine startCol endLine endCol : Nat) : TestResult :=
  .fail {
    message,
    detail? := some detail,
    location? := some {
      moduleName,
      startPos := { line := startLine, column := startCol },
      endPos := { line := endLine, column := endCol } } }
