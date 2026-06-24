/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen

Enumerates the Errata tests defined in a module as a JSON array of their user-facing names. The
Errata test driver runs this per module to discover tests without a hand-maintained list.
-/
module

import Errata
import Lean

set_option doc.verso true

open Lean Errata

/-- Imports a module and returns the user-facing names of the Errata tests it defines. -/
def enumerate (moduleName : String) : IO (Array String) := do
  initSearchPath (← findSysroot)
  let name := moduleName.toName
  let env ← importModules #[{ module := name }] {} (trustLevel := 1024)
  return (testsInModule env name).map fun decl => (privateToUserName decl).toString

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
