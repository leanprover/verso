/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
module

namespace Verso.Elan
set_option doc.verso true

/--
Default environment changes for {name (scope := "VersoUtil.Elan")}`runCmdWithToolchain`.

The main goal is to remove variables that are introduced by Lake.
(We're effectively assuming that if these variables were set, it was by an outer invocation of Lake, and we'd like to undo that.)

Clearing out {lit}`DYLD_LIBRARY_PATH` and {lit}`LD_LIBRARY_PATH` are critical so that when we invoke Elan with a different toolchain, it doesn't look for the wrong shared libraries.
-/
def lakeVars :=
  #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
    "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
    "LEAN", "ELAN", "ELAN_HOME", "LEAN_GITHASH",
    "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"].map (·, none)
  ++ #[("LAKE_RESTORE_ARTIFACTS", some "true")]


/--
Validate that a directory has the shape of a lean project,
return the toolchain (from {lit}`lean-toolchain` or from the override)
-/
public def getProjectToolchain (projectDir : System.FilePath) (overrideToolchain : Option String := none) : IO String := do
  let lakefileLean := projectDir / "lakefile.lean"
  let lakefileToml := projectDir / "lakefile.toml"
  if !(← lakefileLean.pathExists) && !(← lakefileToml.pathExists) then
    throw <| .userError s!"Neither {lakefileLean} nor {lakefileToml} exist, couldn't load project"
  match overrideToolchain with
    | none =>
      let toolchainFile := projectDir / "lean-toolchain"
      if !(← toolchainFile.pathExists) then
        throw <| .userError s!"File {toolchainFile} doesn't exist, couldn't load project"
      return (← IO.FS.readFile toolchainFile).trimAscii.copy
    | some override => return override

/--
Appropriately constructs arguments for spawning a process that approximates executing the following:

```
$ cd projectDir
$ elan run --install <toolchain> <cmd>
```

The function manipulates environment variables to allow {lit}`elan` to be invoked in a process that may itself have be invoked via {lit}`lake`.
Also sets the {lit}`LAKE_RESTORE_ARTIFACTS` environment variable true.
The optional {name}`env` argument allows for additional changes to the environment, which will overwrite the changes made by default.
-/
public def getSpawnArgsForToolchain (projectDir : System.FilePath) (toolchain : String)
    (cmd : Array String)
    (env : Array (String × Option String) := #[])
    : IO.Process.SpawnArgs :=
  let filteredLakeVars := lakeVars.filter (fun (lakeVar, _) => env.all (·.1 != lakeVar))
  {
    cmd := "elan"
    args := #["run", "--install", toolchain] ++ cmd
    cwd := projectDir
    env := filteredLakeVars ++ env,
  }


/--
Executes a command in an environment set up for Lake, specifying the project and toolchain.

Invoking {lean}`runCmdWithToolchain projectDir toolchain #["foo", "bar"]` approximates executing the following:

```
$ cd projectDir
$ elan run --install <toolchain> foo bar
```

The function manipulates environment variables (see {name}`getSpawnArgsForToolchain`.
Also checks the exit code; if it is nonzero, and writes to stderr and throws an error.
-/
public def runCmdWithToolchain (projectDir : System.FilePath) (toolchain : String)
    (cmd : Array String)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  let res ← IO.Process.output (getSpawnArgsForToolchain projectDir toolchain cmd env)
  if res.exitCode != 0 then
    IO.eprintln <|
      "Build process failed executing a command on a specified toolchain." ++
      "\nCWD: " ++ projectDir.toString ++
      "\nToolchain: " ++ toolchain ++
      "\nCommand: " ++ repr cmd ++
      "\nExit code: " ++ toString res.exitCode ++
      "\nstdout: " ++ res.stdout ++
      "\nstderr: " ++ res.stderr

    throw <| .userError <|
      "Build process failed." ++
      decorateOut "stdout" res.stdout ++
      decorateOut "stderr" res.stderr
  return res

where
  decorateOut (name : String) (out : String) : String :=
    if out.isEmpty then "" else s!"\n{name}:\n{out}\n"
