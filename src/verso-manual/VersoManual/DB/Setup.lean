/-
Copyright (c) 2025-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual.DB.Config

/-! # Doc Source Workspace Setup

Executable that manages the doc-gen4 build workspace. Called by the `docSource` Lake package facet.

Usage: `verso-docgen-setup <workspace-dir> <docgen4-dir> <project-dir> [toml-path]`

This executable:
1. Parses `doc-sources.toml` (if provided and exists)
2. Generates a `lakefile.lean` and `lean-toolchain` in the managed workspace
3. Runs any configured setup commands
4. Runs `lake build` to produce `api-docs.db`
5. Verifies the database was produced
-/

open Verso.Genre.Manual.DocSource

/--
Lake environment variables to clear when spawning a child `lake` process, to avoid inheriting
the parent Lake's workspace configuration.
-/
private def lakeVars : Array String :=
  #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
    "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
    "LEAN_GITHASH",
    "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]

/-- Environment variable settings that unset all Lake variables and disable doc-gen4 source links. -/
private def cleanEnv : Array (String × Option String) :=
  lakeVars.map (·, none) ++ #[("DOCGEN_SRC", some "file")]

/-- Reads the `lean-toolchain` file from a directory. -/
private def readToolchain (dir : System.FilePath) : IO String := do
  let tcPath := dir / "lean-toolchain"
  unless ← tcPath.pathExists do
    throw <| .userError s!"lean-toolchain not found at {tcPath}"
  let contents ← IO.FS.readFile tcPath
  return contents.trimAscii.toString

/-- Runs a shell command in the given directory, printing output and throwing on failure. -/
private def runCmd (cmd : String) (args : Array String) (cwd : System.FilePath) : IO Unit := do
  IO.println s!"  Running: {cmd} {" ".intercalate args.toList}"
  let result ← IO.Process.output {
    cmd, args, cwd := some cwd
    env := cleanEnv
  }
  unless result.stdout.isEmpty do IO.print result.stdout
  unless result.stderr.isEmpty do IO.eprint result.stderr
  unless result.exitCode == 0 do
    throw <| .userError s!"Command '{cmd}' exited with code {result.exitCode}"

/-- Checks for a toolchain mismatch between the project and any path dependencies. -/
private def checkToolchainMismatch
    (projectDir : System.FilePath) (config : Config) : IO (Option String) := do
  let ourTc ← readToolchain projectDir
  for req in config.require do
    if let some path := req.path then
      let depDir := if path.isAbsolute then path else projectDir / path
      let depTcPath := depDir / "lean-toolchain"
      if ← depTcPath.pathExists then
        let depTc ← IO.FS.readFile depTcPath
        let depTc := depTc.trimAscii.toString
        if depTc != ourTc then
          return some s!"Toolchain mismatch: this project uses '{ourTc}' but '{req.name}' uses '{depTc}'. The documented library must build with the same toolchain as your Verso project."
  return none

def main (args : List String) : IO UInt32 := do
  -- Parse arguments
  let (wsDir, docgen4Dir, projectDir, tomlPath?) ← match args with
    | [ws, dg, proj, toml] =>
      let r : System.FilePath × System.FilePath × System.FilePath × Option System.FilePath :=
        (⟨ws⟩, ⟨dg⟩, ⟨proj⟩, some ⟨toml⟩)
      pure r
    | [ws, dg, proj] =>
      let r : System.FilePath × System.FilePath × System.FilePath × Option System.FilePath :=
        (⟨ws⟩, ⟨dg⟩, ⟨proj⟩, none)
      pure r
    | _ =>
      IO.eprintln "Usage: verso-docgen-setup <workspace-dir> <docgen4-dir> <project-dir> [toml-path]"
      return 1

  -- Parse doc-sources.toml if provided and exists
  let config? ← do
    if let some (tomlPath : System.FilePath) := tomlPath? then
      if ← tomlPath.pathExists then
        some <$> Config.load tomlPath
      else
        pure none
    else
      pure none

  -- Create workspace directory
  IO.FS.createDirAll wsDir

  -- Write lakefile.lean
  let lakefileContent := generateLakefile config? docgen4Dir projectDir
  IO.FS.writeFile (wsDir / "lakefile.lean") lakefileContent
  IO.println s!"Wrote {wsDir / "lakefile.lean"}"

  -- Write lean-toolchain
  let toolchain ← readToolchain projectDir
  IO.FS.writeFile (wsDir / "lean-toolchain") (toolchain ++ "\n")
  IO.println s!"Wrote {wsDir / "lean-toolchain"} ({toolchain})"

  -- Run setup commands
  if let some config := config? then
    for cmd in config.setup do
      if let some (exe, cmdArgs) := splitCommand cmd then
        runCmd exe cmdArgs wsDir

  -- Run lake build
  let libraries := config?.map (·.libraries) |>.getD #[]
  let targets := if libraries.isEmpty
    then #[":docInfo"]
    else libraries.map (· ++ ":docInfo")

  IO.println s!"Building documentation sources..."
  try
    runCmd "lake" (#["build"] ++ targets) wsDir
  catch e =>
    -- On build failure, check for toolchain mismatch
    if let some config := config? then
      if let some mismatchMsg ← checkToolchainMismatch projectDir config then
        IO.eprintln s!"Note: {mismatchMsg}"
    throw e

  -- Verify the database was produced inside the sub-workspace's build directory.
  let dbPath := wsDir / ".lake" / "build" / "api-docs.db"
  unless ← dbPath.pathExists do
    IO.eprintln s!"Documentation database not found at {dbPath} after build."
    IO.eprintln "This may indicate an incompatible doc-gen4 version or misconfigured library targets."
    IO.eprintln s!"Try running 'cd {wsDir} && lake build' manually to diagnose."
    return 1

  IO.println s!"Documentation database ready at {dbPath}"
  return 0
