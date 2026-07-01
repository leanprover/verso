/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Verso
import Errata

open Verso Errata

/-!
Tests for Verso's build log: where a message's location and severity are recorded, how locations
format, and how logging interacts with the exit code and the ambient output streams.
-/

/-- A message logged with a `pos` location is saved with that file and position. -/
@[test]
def savesPosition : Test := do
  let logger ← Logger.new
  let pos : Lean.Lsp.Position := { line := 4, character := 2 }
  (reportError "boom" (some { file := "PosSave.lean", span := .pos pos }) : BuildLogT IO Unit).run logger
  let errs ← logger.errors
  let some m := errs[0]?
    | fail s!"expected 1 saved error, got {errs.size}"
  assert (m.severity == .error) "expected error severity"
  match m.loc with
  | some { file := "PosSave.lean", span := .pos p } =>
    assertEq 4 p.line
    assertEq 2 p.character
  | _ => fail "expected a saved `PosSave.lean` `pos` location"

/-- A `range` span is likewise saved. -/
@[test]
def savesRange : Test := do
  let logger ← Logger.new
  let r : Lean.Lsp.Range :=
    { start := { line := 1, character := 0 }, «end» := { line := 1, character := 5 } }
  (reportWarning "careful" (some { file := "RangeSave.lean", span := .range r }) : BuildLogT IO Unit).run logger
  let some w := (← logger.warnings)[0]?
    | fail "expected 1 saved warning"
  match w.loc with
  | some { span := .range _, .. } => pure ()
  | _ => fail "expected a `range` span to be saved"

/--
Range formatting defers to Lean's `mkErrorStringWithPos`: `file:line:col-line:col`, with a 1-based
line and 0-based column, keeping the full end position even within one line.
-/
@[test]
def rangeFormat : Test := do
  let crossLine : LogMessage := {
    severity := .error, text := "msg",
    loc := some {
      file := "CrossLine.lean",
      span := .range { start := { line := 19, character := 4 }, «end» := { line := 20, character := 7 } }
    }
  }
  assertEq "CrossLine.lean:20:4-21:7: msg" crossLine.format
  let sameLine : LogMessage := {
    severity := .error, text := "msg",
    loc := some {
      file := "SameLine.lean",
      span := .range { start := { line := 42, character := 4 }, «end» := { line := 42, character := 21 } }
    }
  }
  assertEq "SameLine.lean:43:4-43:21: msg" sameLine.format

/-- A located message is formatted uniformly as `file:line:col: text` on stderr. -/
@[test]
def fileLocationFormat : Test := do
  let logger ← Logger.new
  let out ← captureOutput <|
    (reportError "bad term" (some { file := "FileLoc.lean", span := .pos { line := 6, character := 3 } })
      : BuildLogT IO Unit).run logger
  let some m := (← logger.errors)[0]?
    | fail "expected 1 saved error with a file location"
  assertEq (some "FileLoc.lean") (m.loc.map (·.file))
  assertContains "FileLoc.lean:7:3: bad term" out.stderr

/-- Errors set a non-zero exit code; warnings do not. -/
@[test]
def exitCode : Test := do
  let withErrors ← Logger.new
  (do reportError "e1"; reportWarning "w1"; reportError "e2" : BuildLogT IO Unit).run withErrors
  assertEq 2 (← withErrors.errors).size
  assertEq 1 (← withErrors.warnings).size
  assertEq 1 (← withErrors.exitCode)
  let warningOnly ← Logger.new
  (reportWarning "just a warning" : BuildLogT IO Unit).run warningOnly
  assertEq 0 (← warningOnly.exitCode)

/--
Logging writes to the ambient stderr, resolved at log time: a logger created before a stderr
redirection still writes into the redirected stream, and nothing goes to stdout.
-/
@[test]
def ambientStderr : Test := do
  let logger ← Logger.new
  let out ← captureOutput do
    (do
      reportError "first problem" (some { file := "X.lean", span := .pos { line := 0, character := 0 } })
      reportWarning "second problem" : BuildLogT IO Unit).run logger
  assertContains "X.lean:1:0: first problem" out.stderr
  assertContains "second problem" out.stderr
  assertEq "" out.stdout
  assertEq 1 (← logger.errors).size
  assertEq 1 (← logger.warnings).size
