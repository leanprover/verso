/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
module

namespace Verso.Elan
set_option doc.verso true

/--
Modifies a default set of changes to an environment.
-/
public inductive EnvOverride : Type where
  | /-- Remove the default modification that would otherwise have been added -/
    inherit : EnvOverride
  | /-- Unset the environment variable -/
    unset : EnvOverride
  | /-- Set the environment variable to {lit}`"dev"` -/
    set : String → EnvOverride


/--
Environment variables that we want to clear to call {lit}`elan` with a different toolchain.

We will be generally assuming that, if these variables were set, they were set by an outer invocation of Lake, and we'd like to undo that.
-/
def elanClearVars :=
  #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
    "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
    "LEAN",
    "ELAN_TOOLCHAIN",
    /-
    If `LEAN_GITHASH` is not in place, the wrong value gets embedded in oleans and we end up with
    lots of spurious rebuilds and slow behavior
    -/
    "LEAN_GITHASH",
    /-
    Clearing out `DYLD_LIBRARY_PATH` and `LD_LIBRARY_PATH` are critical so that when we invoke Elan
    with a different toolchain, it doesn't look for the wrong shared libraries.
    -/
    "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]

/--
Lake's artifact cache will prevent certain artifacts from being built if they already exist in the cache.

If the purpose of a command is to put artifacts in the build directory where later steps can find them, then {lit}`"LAKE_RESTORE_ARTIFACTS"` must be set.
Setting this environment variable causes Lake to copy any cached artifacts to the build directory.
See the {manual section "lake-config-toml"}[documentation for {lit}`restoreAllArtifacts`] for details.
-/
def elanVars : (restoreArtifacts : Bool) → Array (String × Option String)
  | false => elanClearVars.map (·, none)
  | true => elanClearVars.map (·, none) ++ #[("LAKE_RESTORE_ARTIFACTS", some "true")]


/--
Validates that a directory has the shape of a lean project, and returns the toolchain (from {lit}`lean-toolchain` or from the override)
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

The function returns an {name}`IO.Process.SpawnArgs` object that resets environment variables appropriately and calls the given {lean}`cmd` via `elan run`.

In Verso, these commands are typically run in with the expectation that they will cause a compilation artifact to be placed in the `.lake` directory.
Passing {name}`restoreArtifacts` defaults the {manual section "lake-config-toml"}[{lit}`LAKE_RESTORE_ARTIFACTS` environment variable] to {lean}`"true"`; this is necessary to ensure that commands like `lake build` actually put those artifacts into place in the build directory.
Otherwise, Lake redirects callers to its cache without copying the artifacts to the build directory.

The optional {name}`env` argument allows for further environment modifications, which will overwrite the default changes.
-/
public def getSpawnArgsForToolchain (projectDir : System.FilePath) (toolchain : String)
    (cmd : Array String)
    (restoreArtifacts : Bool := false)
    (env : Array (String × EnvOverride) := #[])
    : IO.Process.SpawnArgs :=
  let filteredLakeVars := (elanVars restoreArtifacts).filter (fun (envVar, _) => env.all (·.1 != envVar))
  let filteredEnv := env.filterMap fun
    | (_, .inherit) => none
    | (envVar, .unset) => some (envVar, none)
    | (envVar, .set v) => some (envVar, some v))
  {
    cmd := "elan"
    args := #["run", "--install", toolchain] ++ cmd
    cwd := projectDir
    env := filteredLakeVars ++ filteredEnv,
  }


/--
Executes a command in an environment set up for Lake, specifying the project and toolchain.

Invoking {lean}`runCmdWithToolchain projectDir toolchain #["foo", "bar"]` approximates executing the following:

```
$ cd projectDir
$ elan run --install <toolchain> foo bar
```

The function manipulates environment variables (see {name}`getSpawnArgsForToolchain`.

The exit code is checked; if it is nonzero, and writes to stderr and throws an error.
-/
public def runCmdWithToolchain (projectDir : System.FilePath) (toolchain : String)
    (cmd : Array String)
    (restoreArtifacts : Bool := false)
    (env : Array (String × EnvOverride) := #[])
    (errorsToStderr : Bool := true) : IO IO.Process.Output := do
  let res ← IO.Process.output
    (getSpawnArgsForToolchain projectDir toolchain cmd restoreArtifacts env)
  if res.exitCode != 0 then
    let errorDetails : String :=
      "Failure while executing a command on a lean project." ++
        "\nProject directory: " ++ projectDir.toString ++
        "\nToolchain: " ++ toolchain ++
        "\nCommand: " ++ toString (repr cmd) ++
        "\nExit code: " ++ toString res.exitCode ++
        "\nstdout: " ++ res.stdout ++
        "\nstderr: " ++ res.stderr

    if errorsToStderr then
      IO.eprintln errorDetails

      throw <| .userError <|
        "Build process failed." ++
        decorateOut "stdout" res.stdout ++
        decorateOut "stderr" res.stderr
    else
      throw <| .userError errorDetails

  return res

where
  decorateOut (name : String) (out : String) : String :=
    if out.isEmpty then "" else s!"\n{name}:\n{out}\n"
