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
# Document Source Configuration

Parsing for `doc-sources.toml`, which declares which libraries' documentation should be built by
the `docSource` Lake package facet and thus made available in Verso documents.
-/

namespace Verso.Genre.Manual.DocSource

open Lake.Toml

/-- Parsed contents of a `doc-sources.toml` file. -/
structure Config where
  /-- Which library targets to process. -/
  libraries : Array String := #[]
  /--
  Whether to include declarations from the Lean core libraries (`Init`, `Std`, `Lake`, `Lean`).
  -/
  includeCore : Bool := false
deriving Repr, BEq, Inhabited

/-- Extracts a `String` from a TOML `Value`, or throws if it's not a string. -/
private def tomlString : Value → Except String String
  | .string _ s => pure s
  | v => throw s!"expected string, got {v}"

/-- Extracts an `Array String` from a TOML array of strings. -/
private def tomlStringArray : Value → Except String (Array String)
  | .array _ vs => vs.mapM tomlString
  | v => throw s!"expected array of strings, got {v}"

/-- Extracts a `Bool` from a TOML `Value`, or throws if it's not a boolean. -/
private def tomlBool : Value → Except String Bool
  | .boolean _ b => pure b
  | v => throw s!"expected boolean, got {v}"

/-- Parses a `Config` from a TOML `Table`. -/
def Config.ofToml (table : Table) : Except String Config := do
  let libraries ← match table.find? `libraries with
    | some v => tomlStringArray v
    | none => pure #[]
  let includeCore ← match table.find? `include_core with
    | some v => tomlBool v
    | none => pure false
  pure { libraries, includeCore }

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
