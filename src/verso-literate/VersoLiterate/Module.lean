/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Verso.BEq
public import VersoLiterate.Exported
public import Verso.Doc
import VersoUtil.Elan

public section

namespace VersoLiterate
open Lean
open Verso.Doc

def loadJsonString (jsonString : String) (blame := "JSON string") : Except String LitMod := do
  let json ← Lean.Json.parse jsonString |>.mapError (s!"Error parsing {blame}: {·}")
  let name ← json.getObjValAs? String "module" |>.mapError (s!"Error decoding module name in {blame}: {·}")
  let itemsJson ← json.getObjVal? "items" |>.mapError (s!"Error decoding items in {blame}: {·}")
  let eItems ← FromJson.fromJson? (α := VersoLiterate.ExportedModuleItems) itemsJson |>.mapError (s!"Error decoding {blame}: {·}")
  let items ← eItems.toModuleItems
  let images := (json.getObjValAs? (Array String) "images").toOption.getD #[]
  pure { name := name.toName, contents := items, images }

def loadJsonString! (jsonString : String) (blame := "JSON string") : LitMod :=
  match loadJsonString jsonString blame with
  | .error e => panic! e
  | .ok v => v

def load (jsonFile : System.FilePath) : IO LitMod := do
  let json ← IO.FS.readFile jsonFile
  match loadJsonString json (blame := jsonFile.toString) with
  | .error e => throw <| .userError e
  | .ok v => pure v

def modToPage! [LoadLiterate g] (mod : LitMod) (title : Array (Inline g)) (titleString : String) (metadata? : Option g.PartMetadata) : VersoDoc g :=
  match modToPage mod title titleString metadata? with
  | .error e => panic! s!"Couldn't load {titleString}: {e}"
  | .ok v => v

open System in
def loadModuleJson
    (leanProject : FilePath) (mod : String)
    (overrideToolchain : Option String := none) : IO String := do

  let projectDir := ((← IO.currentDir) / leanProject).normalize
  let toolchain ← Verso.Elan.getProjectToolchain projectDir (overrideToolchain := overrideToolchain)

  let res ← Verso.Elan.runCmdWithToolchain projectDir toolchain #["lake", "query", s!"+{mod}:literate"]
  if let some f := res.stdout.splitToList (· == '\n') |>.find? (!·.isEmpty) then
    IO.FS.readFile f
  else throw <| .userError s!"No result returned from build of {mod}"
