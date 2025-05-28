/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Helper
import SubVerso.Module
import MD4Lean
import Verso.Code.External.Env

open Lean

open SubVerso.Highlighting
open SubVerso.Helper
open SubVerso.Module

namespace Verso.Code.External

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

register_option verso.externalExamples.suppressedNamespaces : String := {
  defValue := "",
  descr := "Namespaces to be hidden in term metadata (separated by spaces)",
  group := "verso"
}


initialize registerTraceClass `Elab.Verso.Code.External

initialize registerTraceClass `Elab.Verso.Code.External.loadModule

variable [Monad m] [MonadLift IO m] [MonadEnv m] [MonadOptions m] [MonadError m] [MonadTrace m] [AddMessageContext m] [MonadFinally m] [MonadAlwaysExcept ε m]


open System in
def loadModuleContent' (projectDir : String) (mod : String) (suppressNamespaces : List String) : m (Array ModuleItem) := do

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
      "LEAN", "ELAN", "ELAN_HOME", "LEAN_GITHASH",
      "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]


  let toolchainFile ← IO.FS.Handle.mk toolchainfile .read
  toolchainFile.lock (exclusive := true)
  let (h, f) ← IO.FS.createTempFile
  try
    let cmd := "elan"

    withTraceNode `Elab.Verso.Code.External.loadModule (fun _ => pure m!"loadModuleContent': building example project's module") do
      let args := #["run", "--install", toolchain, "lake", "build", "+" ++ mod]
      let res ← IO.Process.output {
        cmd, args, cwd := projectDir
        -- Unset Lake's environment variables
        env := lakeVars.map (·, none)
      }
      if res.exitCode != 0 then reportFail projectDir cmd args res

    withTraceNode `Elab.Verso.Code.External.loadModule (fun _ => pure m!"loadModuleContent': extracting '{mod}'") do
      IO.FS.withTempFile fun h f' => do
        h.putStrLn <| " ".intercalate suppressNamespaces
        h.flush
        h.rewind
        let args :=
          #["run", "--install", toolchain, "lake", "exe", "subverso-extract-mod"] ++
          #["--suppress-namespaces", f'.toString] ++
          #[mod, f.toString]
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

def getSuppress : m (List String) := do
  let some nss ← verso.externalExamples.suppressedNamespaces.get? <$> getOptions
    | return []
  let nss := nss.dropWhile (· == '"') |>.dropRightWhile (· == '"') -- Strings getting double-quoted for some reason
  return nss.splitOn " "

def loadModuleContent [MonadAlwaysExcept ε m] (mod : String) : m (Array ModuleItem) :=
  withTraceNode `Elab.Verso.Code.External (fun _ => pure m!"Loading example module {mod}") <| do
    let modName := mod.toName
    let suppress ← getSuppress
    if let some ms := (loadedModulesExt.getState (← getEnv)).find? modName then
      if let some m := ms[suppress]? then
        trace[Elab.Verso.Code.External] m!"Cache hit for {mod}"
        return m

    let traceMsg (r : Except ε (Array ModuleItem × Nat)) : m MessageData :=
      match r with
      | .error .. => pure m!"Cache miss for {mod} but failed to load it"
      | .ok (_, ms) => pure m!"Cache miss for {mod}, loaded in {ms.toFloat / 1000.0}s"
    Prod.fst <$> withTraceNode `Elab.Verso.Code.External.loadModule traceMsg do
      let projectDir ← getProjectDir
      let ms1 ← IO.monoMsNow
      let items ← loadModuleContent' projectDir mod suppress
      let ms2 ← IO.monoMsNow
      modifyEnv fun env =>
        loadedModulesExt.modifyState env fun st =>
          let forMod := st.find? modName |>.getD {}
          let forMod := forMod.insert suppress items
          st.insert modName forMod
      return (items, ms2 - ms1)
