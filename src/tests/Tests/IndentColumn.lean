/-
Copyright (c) 2025-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual.Docstring.Show

open Verso.Genre.Manual

private def assertEqual (label : String) (expected actual : Nat) : IO Unit := do
  unless expected == actual do
    throw <| IO.userError s!"{label}: expected {expected} but got {actual}"

private def testIndentColumnEmpty : IO Unit :=
  assertEqual "empty string" 0 (indentColumn "")

private def testIndentColumnNoIndent : IO Unit :=
  assertEqual "no indent" 0 (indentColumn "abc")

private def testIndentColumnSimple : IO Unit :=
  assertEqual "simple indent" 3 (indentColumn "   abc")

private def testIndentColumnUniform : IO Unit :=
  assertEqual "uniform indent" 3 (indentColumn "   abc\n\n   def")

private def testIndentColumnMinimum : IO Unit :=
  assertEqual "minimum indent" 2 (indentColumn "   abc\n\n  def")

private def testIndentColumnMultiline : IO Unit :=
  assertEqual "multiline minimum" 2 (indentColumn "   abc\n\n  def\n    a")

private def indentColumnTests : List (String × IO Unit) := [
  ("indentColumn: empty string", testIndentColumnEmpty),
  ("indentColumn: no indent", testIndentColumnNoIndent),
  ("indentColumn: simple indent", testIndentColumnSimple),
  ("indentColumn: uniform indent", testIndentColumnUniform),
  ("indentColumn: minimum indent", testIndentColumnMinimum),
  ("indentColumn: multiline minimum", testIndentColumnMultiline),
]

public def runIndentColumnTests : IO Nat := do
  IO.println "Running indentColumn tests..."
  let mut failures := 0
  for (name, test) in indentColumnTests do
    IO.print s!"  {name}: "
    try
      test
      IO.println "ok"
    catch e =>
      IO.println s!"FAIL\n    {e}"
      failures := failures + 1
  return failures
