import Verso.BEq
import VersoLiterate.Exported

namespace VersoLiterate
open Lean

structure LitMod where
  name : Name
  contents : Array ModuleItem'
deriving Inhabited, Repr

open Verso.BEq in
instance : BEq LitMod where
  beq := ptrEqThen fun
    | ⟨name1, contents1⟩, ⟨name2, contents2⟩ =>
      name1 == name2 && contents1 == contents2

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
