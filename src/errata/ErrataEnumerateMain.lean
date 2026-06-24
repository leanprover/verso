/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen

Enumerates the Errata tests defined in a module as a JSON array of objects, each with the test's
user-facing name and its source range. The Errata test driver runs this per module to discover
tests, and seeds each test's failure location with its range.
-/
module

import Errata
import Lean

set_option doc.verso true

open Lean Errata

/-- Imports a module and returns its Errata tests, each as a JSON object of name and source range. -/
def enumerate (moduleName : String) : IO (Array Json) := do
  initSearchPath (← findSysroot)
  let name := moduleName.toName
  let env ← importModules #[{ module := name }] {} (trustLevel := 1024)
  return (testsInModule env name).map fun decl =>
    let userName := (privateToUserName decl).toString
    let range := declRangeExt.find? (level := .server) env decl
    let pos := (range.map (·.range.pos)).getD ⟨0, 0⟩
    let endPos := (range.map (·.range.endPos)).getD ⟨0, 0⟩
    json%{
      "name": $userName,
      "startLine": $pos.line, "startColumn": $pos.column,
      "endLine": $endPos.line, "endColumn": $endPos.column
    }

/-- Enumerates a module's tests, writing or printing the JSON manifest. -/
public def main (args : List String) : IO UInt32 := do
  match args with
  | [moduleName, outPath] =>
    let tests ← enumerate moduleName
    if let some parent := (System.FilePath.mk outPath).parent then
      IO.FS.createDirAll parent
    IO.FS.writeFile outPath ((toJson tests).pretty ++ "\n")
    return 0
  | [moduleName] =>
    IO.println (toJson (← enumerate moduleName)).pretty
    return 0
  | _ =>
    IO.eprintln "usage: errata-enumerate MODULE [OUTPUT]"
    return 1
