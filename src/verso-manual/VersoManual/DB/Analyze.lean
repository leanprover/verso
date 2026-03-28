/-
Copyright (c) 2025-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import DocGen4
import SQLite
import VersoManual.DB.Config

/-! # Doc Source Analysis

Executable that runs doc-gen4's analysis on pre-built `.olean` files and writes the results to a
SQLite database. Called by the `docSource` Lake package facet.

Usage: `verso-docgen-analyze <build-dir> <db-file> [--core] [--toml <path>] [<module> ...]`

Unlike the previous `verso-docgen-setup` approach, this does not create a nested Lake workspace.
It calls doc-gen4's API directly, relying on `LEAN_PATH` (set by Lake via `getAugmentedEnv`) to
locate the `.olean` files.
-/

open DocGen4 DocGen4.Process DocGen4.DB

/-- Flush the WAL so the database file is self-contained. -/
private def walCheckpoint (dbPath : System.FilePath) : IO Unit := do
  let db ← SQLite.open dbPath.toString
  db.exec "PRAGMA wal_checkpoint(TRUNCATE)"
  db.exec "PRAGMA optimize"

/-- Parse command-line arguments into structured options. -/
private structure Args where
  buildDir : String
  dbFile : String
  includeCore : Bool
  tomlPath : Option System.FilePath
  modules : List Lean.Name
deriving Inhabited

private def parseArgs : List String → IO Args
  | buildDir :: dbFile :: rest => do
    let mut includeCore := false
    let mut tomlPath : Option System.FilePath := none
    let mut moduleArgs : List String := []
    let mut remaining := rest
    while !remaining.isEmpty do
      match remaining with
      | "--core" :: tail =>
        includeCore := true
        remaining := tail
      | "--toml" :: path :: tail =>
        tomlPath := some ⟨path⟩
        remaining := tail
      | arg :: tail =>
        moduleArgs := moduleArgs ++ [arg]
        remaining := tail
      | [] => break
    pure {
      buildDir, dbFile, includeCore, tomlPath
      modules := moduleArgs.map String.toName
    }
  | _ => throw <| .userError
    "Usage: verso-docgen-analyze <build-dir> <db-file> [--core] [--toml <path>] [<module> ...]"

unsafe def main (args : List String) : IO UInt32 := do
  let opts ← parseArgs args

  -- Read additional modules from doc-sources.toml if provided
  let tomlModules ← do
    if let some tomlPath := opts.tomlPath then
      let config ← Verso.Genre.Manual.DocSource.Config.load tomlPath
      -- Library names in the TOML are treated as module prefixes to analyze
      pure <| config.libraries.toList.map String.toName
    else
      pure []
  let allModules := opts.modules ++ tomlModules

  if allModules.isEmpty && !opts.includeCore then
    IO.eprintln "No modules to analyze. Provide module names, --toml, or --core."
    return 1

  -- Generate core documentation (Init, Std, Lake, Lean)
  if opts.includeCore then
    for coreModule in [`Init, `Std, `Lake, `Lean] do
      IO.println s!"Analyzing core module: {coreModule}"
      let doc ← load <| .analyzePrefixModules coreModule
      updateModuleDb builtinDocstringValues doc opts.buildDir opts.dbFile none

  -- Generate documentation for specified modules (each as a prefix analysis)
  for mod in allModules do
    IO.println s!"Analyzing module prefix: {mod}"
    let doc ← load <| .analyzePrefixModules mod
    updateModuleDb builtinDocstringValues doc opts.buildDir opts.dbFile none

  -- Flush WAL so the database file is self-contained for readers
  let dbPath : System.FilePath := opts.buildDir / opts.dbFile
  walCheckpoint dbPath

  IO.println s!"Documentation database ready at {dbPath}"
  return 0
