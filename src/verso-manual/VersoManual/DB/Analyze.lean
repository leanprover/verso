/-
Copyright (c) 2025-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import DocGen4.DB

import DocGen4.Load
import Lean.DocString
import Lean.Parser.Extension
import SQLite
import VersoManual.DB
import VersoManual.DB.Config



public section

/-!
# Doc Source Analysis

Executable that runs doc-gen4's analysis on pre-built `.olean` files and writes the results to a
SQLite database. Called by the `docSource` Lake package facet.

Usage: `verso-docgen-analyze <build-dir> <db-file> [--core] [--toml <path>] [<module> ...]`

Unlike the previous `verso-docgen-setup` approach, this does not create a nested Lake workspace.
It calls doc-gen4's API directly, relying on `LEAN_PATH` (set by Lake via `getAugmentedEnv`) to
locate the `.olean` files.
-/

open DocGen4 Process
open Lean

/--
Collects conv tactics from the environment and writes them to the database.

This is a temporary measure until doc-gen4 is updated to collect conv tactics.
Conv tactics are stored in their own `conv_tactics` table, separate from the regular `tactics`
table, because regular tactics have additional machinery (aliases, tags, extension docs, custom
names) that conv tactics don't yet have.
-/
private def saveConvTactics (env : Environment) (buildDir dbFile : String) : IO Unit := do
  let dbPath : System.FilePath := buildDir / dbFile
  let sqlite ← SQLite.open dbPath.toString
  sqlite.exec
    "CREATE TABLE IF NOT EXISTS conv_tactics (
      module_name TEXT NOT NULL,
      internal_name TEXT NOT NULL,
      user_name TEXT NOT NULL,
      doc_string TEXT NOT NULL,
      PRIMARY KEY (module_name, internal_name)
    )"
  let stmt ← sqlite.prepare
    "INSERT OR IGNORE INTO conv_tactics (module_name, internal_name, user_name, doc_string) VALUES (?, ?, ?, ?)"
  let some convs := (Parser.parserExtension.getState env).categories.find? `conv
    | return
  for ⟨kind, ()⟩ in convs.kinds do
    let some modIdx := env.getModuleIdxFor? kind | continue
    let moduleName := env.header.moduleNames[modIdx]!
    let docString := (← findDocString? env kind).getD ""
    let userName := kind.getString!
    stmt.bind 1 moduleName.toString
    stmt.bind 2 kind.toString
    stmt.bind 3 userName
    stmt.bind 4 docString
    let _ ← stmt.step
    stmt.reset
    stmt.clearBindings

/-- Flushes the WAL so the database file is self-contained. -/
private def walCheckpoint (dbPath : System.FilePath) : IO Unit := do
  let db ← SQLite.open dbPath.toString
  db.exec "PRAGMA wal_checkpoint(TRUNCATE)"
  db.exec "PRAGMA optimize"

/-- Parses command-line arguments into structured options. -/
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

def main (args : List String) : IO UInt32 := do
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
      updateModuleDb DB.builtinDocstringValues doc opts.buildDir opts.dbFile none

  -- Generate documentation for specified modules (each as a prefix analysis)
  for mod in allModules do
    IO.println s!"Analyzing module prefix: {mod}"
    let doc ← load <| .analyzePrefixModules mod
    updateModuleDb DB.builtinDocstringValues doc opts.buildDir opts.dbFile none

  -- Collect and store conv tactics (not yet handled by doc-gen4)
  let allPrefixes := (if opts.includeCore then [`Init, `Std, `Lake, `Lean] else []) ++ allModules
  if !allPrefixes.isEmpty then
    IO.println "Collecting conv tactics..."
    let env ← DocGen4.envOfImports allPrefixes.toArray
    saveConvTactics env opts.buildDir opts.dbFile

  -- Flush WAL so the database file is self-contained for readers
  let dbPath : System.FilePath := opts.buildDir / opts.dbFile
  walCheckpoint dbPath

  IO.println s!"Documentation database ready at {dbPath}"
  return 0
