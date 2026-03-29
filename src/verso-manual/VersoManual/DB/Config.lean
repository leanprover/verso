/-
Copyright (c) 2025-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lake.Toml
public import Lake.Toml.Data.Value
public section

/-!
# Doc Source Configuration

Parsing for `doc-sources.toml`, which declares which libraries' documentation should be built by
the `docSource` Lake package facet.
-/

namespace Verso.Genre.Manual.DocSource

open Lake.Toml

/-- Parsed contents of a `doc-sources.toml` file. -/
structure Config where
  /-- Which library targets to document. -/
  libraries : Array String := #[]
deriving Repr, BEq, Inhabited

/-- Extracts a `String` from a TOML `Value`, or `none` if it's not a string. -/
private def tomlString? : Value → Option String
  | .string _ s => some s
  | _ => none

/--
Extracts an `Array String` from a TOML array of strings. Non-string elements are silently
skipped.
-/
private def tomlStringArray? : Value → Option (Array String)
  | .array _ vs => some <| vs.filterMap tomlString?
  | _ => none

/-- Parses a `Config` from a TOML `Table`. -/
def Config.ofToml (table : Table) : Except String Config := do
  let libraries := match table.find? `libraries with
    | some v => tomlStringArray? v |>.getD #[]
    | none => #[]
  pure { libraries }

/-- Loads and parses a `doc-sources.toml` file. -/
def Config.load (filePath : System.FilePath) : IO Config := do
  let input ← IO.FS.readFile filePath
  let ictx := Lean.Parser.mkInputContext input filePath.toString
  match (← Lake.Toml.loadToml ictx |>.toBaseIO) with
  | .ok table =>
    match Config.ofToml table with
    | .ok config => pure config
    | .error e => throw <| .userError s!"Error parsing {filePath}: {e}"
  | .error msgs =>
    let msgStrs ← msgs.toList.mapM fun msg => msg.data.toString
    throw <| .userError s!"Error parsing {filePath}:\n{"\n".intercalate msgStrs}"

end Verso.Genre.Manual.DocSource
