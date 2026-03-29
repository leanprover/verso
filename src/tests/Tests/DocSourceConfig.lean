/-
Copyright (c) 2025-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lake.Toml
import VersoManual.DB.Config

/-!
# Tests for Doc Source Configuration Parsing

Tests for `Verso.Genre.Manual.DocSource.Config` — TOML parsing for `doc-sources.toml`.
-/

open Verso.Genre.Manual.DocSource
open Lake.Toml

/-- Parses a TOML string into a `Table`. Throws on parse error. -/
private def parseToml (input : String) : IO Table := do
  let ictx := Lean.Parser.mkInputContext input "<test>"
  match (← Lake.Toml.loadToml ictx |>.toBaseIO) with
  | .ok table => pure table
  | .error msgs =>
    let msgStrs ← msgs.toList.mapM fun msg => msg.data.toString
    throw <| .userError s!"TOML parse error:\n{"\n".intercalate msgStrs}"

/-- Checks that two values are equal, throwing a descriptive error if not. -/
private def assertEqual [BEq α] [Repr α] (label : String) (expected actual : α) : IO Unit := do
  unless expected == actual do
    throw <| IO.userError s!"{label}: expected\n  {repr expected}\nbut got\n  {repr actual}"

-- ============================================================================
-- Config.ofToml tests
-- ============================================================================

private def testEmptyConfig : IO Unit := do
  let table ← parseToml ""
  let config ← IO.ofExcept <| Config.ofToml table
  assertEqual "empty config libraries" #[] config.libraries

private def testLibrariesField : IO Unit := do
  let table ← parseToml "
libraries = [\"Mathlib\", \"Batteries\"]
"
  let config ← IO.ofExcept <| Config.ofToml table
  assertEqual "libraries" #["Mathlib", "Batteries"] config.libraries

private def testLibrariesOnly : IO Unit := do
  let table ← parseToml "
libraries = [\"Init\"]
"
  let config ← IO.ofExcept <| Config.ofToml table
  assertEqual "libraries only" #["Init"] config.libraries

-- ============================================================================
-- Test runner
-- ============================================================================

private def docSourceConfigTests : List (String × IO Unit) := [
  ("Config.ofToml: empty config", testEmptyConfig),
  ("Config.ofToml: libraries field", testLibrariesField),
  ("Config.ofToml: libraries only", testLibrariesOnly),
]

public def runDocSourceConfigTests : IO Nat := do
  IO.println "Running doc source config tests..."
  let mut failures := 0
  for (name, test) in docSourceConfigTests do
    IO.print s!"  {name}: "
    try
      test
      IO.println "ok"
    catch e =>
      IO.println s!"FAIL\n    {e}"
      failures := failures + 1
  return failures
