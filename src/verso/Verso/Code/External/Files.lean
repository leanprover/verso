/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Options
public import Lean.Environment
public import Lean.Exception
public import Lean.Util.Trace

import SubVerso.Helper
public import SubVerso.Module
import MD4Lean
public import Verso.Code.External.Env
public import VersoUtil.Elan

public section

open Lean

open SubVerso.Highlighting
open SubVerso.Helper
open SubVerso.Module

namespace Verso.Code.External

register_option verso.exampleProject : String := {
  defValue := "",
  descr := "The directory in which to search for example code",
}

register_option verso.exampleModule : String := {
  defValue := "",
  descr := "The default module to load examples from",
}

register_option verso.externalExamples.suppressedNamespaces : String := {
  defValue := "",
  descr := "Namespaces to be hidden in term metadata (separated by spaces)",
}


initialize registerTraceClass `Elab.Verso.Code.External

initialize registerTraceClass `Elab.Verso.Code.External.loadModule

variable [Monad m] [MonadLift IO m] [MonadEnv m] [MonadOptions m] [MonadError m] [MonadTrace m] [AddMessageContext m] [MonadFinally m] [MonadAlwaysExcept ε m]


open System in
def loadModuleContent' (projectDir : StrLit) (mod : String) (suppressNamespaces : List String) : m (Array ModuleItem) := do
  let blame := projectDir

  let projectDir : FilePath := projectDir.getString
  let toolchain ←
    match ← (Elan.getProjectToolchain projectDir).toBaseIO with
      | .ok toolchain => pure toolchain
      | .error e => throwErrorAt blame s!"{e}"

  let runCmd (trace : MessageData) (cmd : Array String) (restoreArtifacts : Bool) : m Unit :=
    withTraceNode `Elab.Verso.Code.External.loadModule (fun _ => pure <| trace.trace {cls := `command} #[m!"{" ".intercalate cmd.toList}"]) do
      let _ ← Verso.Elan.runCmdWithToolchain projectDir toolchain cmd restoreArtifacts
        (env := #[("SUBVERSO_SUPPRESS_NAMESPACES", .set (" ".intercalate suppressNamespaces))])

  let toolchainFile ← IO.FS.Handle.mk (projectDir / "lean-toolchain") .read
  -- Lake tends to get in trouble if used concurrently, so build the Lean code with a lock.
  toolchainFile.lock (exclusive := true)
  try
    runCmd m!"loadModuleContent': building extractor" #["lake", "build", "subverso-extract-mod"] false
    runCmd m!"loadModuleContent': building highlighted example" #["lake", "build", "+" ++ mod ++ ":highlighted"] true
  finally
    toolchainFile.unlock

  let hlDir := ("build" : System.FilePath) / "highlighted"
  let hlFile :=
    (mod.splitToList (· == '.')).foldl (init := hlDir) (· / ·) |>.addExtension "json"
  -- Very old Lake versions don't put things in .lake
  let lakeDir := if (← (projectDir / ".lake").isDir) then projectDir / ".lake" else projectDir
  let json ← IO.FS.readFile (lakeDir / hlFile)
  let json ←
    match Json.parse json with
    | .ok v => pure v
    | .error err => throwError s!"Invalid JSON syntax in {lakeDir / hlFile}. {err}"
  match Module.fromJson? json with
  | .error err =>
    throwError s!"Couldn't deserialize JSON from output file: {err}\nIn:\n{json}"
  | .ok val => pure val.items

def getSuppress : m (List String) := do
  let some nss ← verso.externalExamples.suppressedNamespaces.get? <$> getOptions
    | return []
  let nss := nss.dropWhile (· == '"') |>.dropEndWhile (· == '"') -- Strings getting double-quoted for some reason
  return nss.copy.splitOn " "

def loadModuleContent [MonadAlwaysExcept ε m] (projectDir : StrLit) (mod : String) : m (Array ModuleItem) :=
  withTraceNode `Elab.Verso.Code.External (fun _ => pure m!"Loading example module {mod}") <| do
    let dirName := projectDir.getString
    let modName := mod.toName
    let suppress ← getSuppress
    if let some ms := (loadedModulesExt.getState (← getEnv))[dirName]?.getD {} |>.find? modName then
      if let some m := ms[suppress]? then
        trace[Elab.Verso.Code.External] m!"Cache hit for {mod}"
        return m

    let traceMsg (r : Except ε (Array ModuleItem × Nat)) : m MessageData :=
      match r with
      | .error .. => pure m!"Cache miss for {mod} but failed to load it"
      | .ok (_, ms) => pure m!"Cache miss for {mod}, loaded in {ms.toFloat / 1000.0}s"
    Prod.fst <$> withTraceNode `Elab.Verso.Code.External.loadModule traceMsg do
      let ms1 ← IO.monoMsNow
      let items ← loadModuleContent' projectDir mod suppress
      let ms2 ← IO.monoMsNow
      modifyEnv fun env =>
        loadedModulesExt.modifyState env fun st =>
          st.alter dirName fun ms =>
            let ms := ms.getD {}
            let forMod := ms.find? modName |>.getD {}
            let forMod := forMod.insert suppress items
            some (ms.insert modName forMod)
      return (items, ms2 - ms1)
