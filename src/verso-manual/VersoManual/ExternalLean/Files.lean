/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Helper
import SubVerso.Module
import MD4Lean
import VersoManual.ExternalLean.Env

open Lean

open SubVerso.Highlighting
open SubVerso.Helper
open SubVerso.Module

namespace Verso.Genre.Manual.ExternalLean

register_option verso.exampleProject : String := {
  defValue := "",
  descr := "The directory in which to search for example code",
  group := "verso"
}

register_option verso.exampleModule : String := {
  defValue := "",
  descr := "The default module to load examples from",
  group := "verso"
}

variable [Monad m] [MonadLift IO m] [MonadEnv m] [MonadOptions m] [MonadError m] [MonadTrace m] [AddMessageContext m] [MonadFinally m] [MonadAlwaysExcept ε m]


open System in
def loadModuleContent' (projectDir : String) (mod : String) : m (Array ModuleItem) := do

  let projectDir : FilePath := projectDir

  -- Validate that the path is really a Lean project
  let lakefile := projectDir / "lakefile.lean"
  let lakefile' := projectDir / "lakefile.toml"
  if !(← lakefile.pathExists) && !(← lakefile'.pathExists) then
    throwError m!"Neither {lakefile} nor {lakefile'} exist, couldn't load project"
  let toolchainfile := projectDir / "lean-toolchain"
  let toolchain ← do
      if !(← toolchainfile.pathExists) then
        throwError m!"File {toolchainfile} doesn't exist, couldn't load project"
      pure (← IO.FS.readFile toolchainfile).trim

  -- Kludge: remove variables introduced by Lake. Clearing out DYLD_LIBRARY_PATH and
  -- LD_LIBRARY_PATH is useful so the version selected by Elan doesn't get the wrong shared
  -- libraries.
  let lakeVars :=
    #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
      "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
      "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]


  let toolchainFile ← IO.FS.Handle.mk toolchainfile .read
  toolchainFile.lock (exclusive := true)
  let (h, f) ← IO.FS.createTempFile
  try
    let cmd := "elan"

    withTraceNode `Elab.Verso (fun _ => pure m!"loadModuleContent': building example project") do
      let args := #["run", "--install", toolchain, "lake", "build"]
      let res ← IO.Process.output {
        cmd, args, cwd := projectDir
        -- Unset Lake's environment variables
        env := lakeVars.map (·, none)
      }
      if res.exitCode != 0 then reportFail projectDir cmd args res

    withTraceNode `Elab.Verso (fun _ => pure m!"loadModuleContent': building subverso-extract-mod") do
      let args := #["run", "--install", toolchain, "lake", "env", "which", "subverso-extract-mod"]
      let res ← IO.Process.output {
        cmd, args, cwd := projectDir
        -- Unset Lake's environment variables
        env := lakeVars.map (·, none)
      }
      if res.exitCode != 0 then
        let args := #["run", "--install", toolchain, "lake", "build", "subverso-extract-mod"]

        let res ← IO.Process.output {
          cmd, args, cwd := projectDir
          -- Unset Lake's environment variables
          env := lakeVars.map (·, none)
        }
        if res.exitCode != 0 then reportFail projectDir cmd args res

    withTraceNode `Elab.Verso (fun _ => pure m!"loadModuleContent': extracting '{mod}'") do
      let args := #["run", "--install", toolchain, "lake", "env", "subverso-extract-mod", mod, f.toString]
      let res ← IO.Process.output {
        cmd, args, cwd := projectDir
        -- Unset Lake's environment variables
        env := lakeVars.map (·, none)
      }
      if res.exitCode != 0 then reportFail projectDir cmd args res

    h.rewind

    let .ok (.arr json) := Json.parse (← h.readToEnd)
      | throwError s!"Expected JSON array"
    match json.mapM fromJson? with
    | .error err =>
      throwError s!"Couldn't parse JSON from output file: {err}\nIn:\n{json}"
    | .ok val => pure val
  finally
    toolchainFile.unlock
    IO.FS.removeFile f

where
  decorateOut (name : String) (out : String) : String :=
    if out.isEmpty then "" else s!"\n{name}:\n{out}\n"
  reportFail {α} (projectDir : FilePath) (cmd : String) (args : Array String) (res : IO.Process.Output) : m α := do
    throwError ("Build process failed." ++
      "\nCWD: " ++ projectDir.toString ++
      "\nCommand: " ++ cmd ++
      "\nArgs: " ++ repr args ++
      "\nExit code: " ++ toString res.exitCode ++
      "\nstdout: " ++ res.stdout ++
      "\nstderr: " ++ res.stderr)



def getProjectDir : m String := do
  let some projectDir ← verso.exampleProject.get? <$> getOptions
    | throwError "No example project specified - use `set_option verso.exampleProject \"DIR\" to set it.`"
  return projectDir

def loadModuleContent [MonadAlwaysExcept ε m] (mod : String) : m (Array ModuleItem) :=
  withTraceNode `Elab.Verso (fun _ => pure m!"Loading example module {mod}") <| do
    let modName := mod.toName
    if let some m := (loadedModulesExt.getState (← getEnv)).find? modName then return m
    else
      let projectDir ← getProjectDir

      let items ← loadModuleContent' projectDir mod
      modifyEnv (loadedModulesExt.modifyState · (·.insert modName items))
      return items
