/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso.BEq
import VersoLiterate.Exported
import Verso.Doc

namespace VersoLiterate
open Lean
open Verso.Doc

def loadJsonString (jsonString : String) (blame := "JSON string") : Except String LitMod := do
  let json ← Lean.Json.parse jsonString |>.mapError (s!"Error parsing {blame}: {·}")
  let name ← json.getObjValAs? String "module" |>.mapError (s!"Error decoding module name in {blame}: {·}")
  let itemsJson ← json.getObjVal? "items" |>.mapError (s!"Error decoding items in {blame}: {·}")
  let eItems ← FromJson.fromJson? (α := VersoLiterate.ExportedModuleItems) itemsJson |>.mapError (s!"Error decoding {blame}: {·}")
  let items ← eItems.toModuleItems
  pure { name := name.toName, contents := items }

def loadJsonString! (jsonString : String) (blame := "JSON string") : LitMod :=
  match loadJsonString jsonString blame with
  | .error e => panic! e
  | .ok v => v

def load (jsonFile : System.FilePath) : IO LitMod := do
  let json ← IO.FS.readFile jsonFile
  match loadJsonString json (blame := jsonFile.toString) with
  | .error e => throw <| .userError e
  | .ok v => pure v

def modToPage! [LoadLiterate g] (mod : LitMod) (title : Array (Inline g)) (titleString : String) : VersoDoc g :=
  match modToPage mod title titleString with
  | .error e => panic! s!"Couldn't load {titleString}: {e}"
  | .ok v => v

open System in
def loadModuleJson
    (leanProject : FilePath) (mod : String)
    (overrideToolchain : Option String := none) : IO String := do

  let projectDir := ((← IO.currentDir) / leanProject).normalize

  -- Validate that the path is really a Lean project
  let lakefile := projectDir / "lakefile.lean"
  let lakefile' := projectDir / "lakefile.toml"
  if !(← lakefile.pathExists) && !(← lakefile'.pathExists) then
    throw <| .userError s!"Neither {lakefile} nor {lakefile'} exist, couldn't load project"
  let toolchain ← match overrideToolchain with
    | none =>
      let toolchainfile := projectDir / "lean-toolchain"
      if !(← toolchainfile.pathExists) then
        throw <| .userError s!"File {toolchainfile} doesn't exist, couldn't load project"
      pure (← IO.FS.readFile toolchainfile).trim
    | some override => pure override

  -- Kludge: remove variables introduced by Lake. Clearing out DYLD_LIBRARY_PATH and
  -- LD_LIBRARY_PATH is useful so the version selected by Elan doesn't get the wrong shared
  -- libraries.
  let lakeVars :=
    #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
      "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
      "LEAN_GITHASH",
      "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]
  let cmd := "elan"
  let args := #["run", "--install", toolchain, "lake", "query", s!"+{mod}:literate"]
  let res ← IO.Process.output {
    cmd, args, cwd := projectDir
    -- Unset Lake's environment variables
    env := lakeVars.map (·, none)
  }
  if res.exitCode != 0 then reportFail projectDir cmd args res
  if let some f := res.stdout.splitToList (· == '\n') |>.find? (!·.isEmpty) then
    IO.FS.readFile f
  else throw <| .userError s!"No result returned from build of {mod}"

where
  decorateOut (name : String) (out : String) : String :=
    if out.isEmpty then "" else s!"\n{name}:\n{out}\n"
  reportFail {α} (projectDir : FilePath) (cmd : String) (args : Array String) (res : IO.Process.Output) : IO α := do
    IO.eprintln <|
      "Build process failed." ++
      "\nCWD: " ++ projectDir.toString ++
      "\nCommand: " ++ cmd ++
      "\nArgs: " ++ repr args ++
      "\nExit code: " ++ toString res.exitCode ++
      "\nstdout: " ++ res.stdout ++
      "\nstderr: " ++ res.stderr

    throw <| .userError <|
      "Build process failed." ++
      decorateOut "stdout" res.stdout ++
      decorateOut "stderr" res.stderr
