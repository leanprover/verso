/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lake.Toml
public import Lake.Toml.Data.Value
public import Lake.Toml.Decode
public import Lean.Data.NameMap.Basic

open Lean
open Lake (DecodeToml decodeToml)
open Lake.Toml

public section

namespace VersoLiterate

/-- A target entry from `[[targets]]` in `literate.toml`. -/
structure Target where
  library : Option Name := none
  module : Option Name := none
  package : Option Name := none
deriving Repr, BEq, Inhabited

/-- Site metadata (title, description, favicon). -/
structure Metadata where
  title : Option String := none
  description : Option String := none
  favicon : Option String := none
deriving Repr, BEq, Inhabited

/-- Configuration loaded from `literate.toml`. -/
structure LiterateConfig where
  /-- Explicit targets; if non-empty, replaces default target set. -/
  targets : Array Target := #[]
  /-- Modules (and children) to exclude from the site. -/
  exclude : Array Name := #[]
  /-- Top-level sibling order: listed modules appear first, then alphabetical. -/
  order : Array Name := #[]
  /-- Per-parent ordering of children. -/
  orderChildren : NameMap (Array Name) := {}
  /-- Module whose rendered content becomes the landing page. -/
  landingPage : Option Name := none
  /-- Syntax node kinds to hide (e.g. `Lean.Parser.Command.set_option`). -/
  hideCommands : Array Name := #[]
  /-- Site metadata (title, description, favicon). -/
  metadata : Metadata := {}
  /-- Extra CSS files to include. -/
  extraCss : Array String := #[]
  /-- Extra JS files to include. -/
  extraJs : Array String := #[]
  /-- Whether to show declaration docstrings by default. -/
  showDocstrings : Bool := true
  /-- Declarations whose docstrings should be shown (when `showDocstrings = false`). -/
  showDocstringsFor : Array Name := #[]
  /-- Declarations whose docstrings should be hidden (when `showDocstrings = true`). -/
  hideDocstringsFor : Array Name := #[]
  /-- Syntax kinds whose output (info messages) should be displayed as a separate block. -/
  showOutput : Array Name := #[`Lean.Parser.Command.eval, `Lean.Parser.Command.check, `Lean.Parser.Command.print, `Lean.reduceCmd]
  /-- Whether to show the collapsible imports list on each page. -/
  showImports : Bool := true
deriving Repr, Inhabited

/-- Decode a `[[targets]]` table entry into a `Target`. -/
def decodeTarget (v : Value) : EDecodeM Target := do
  let t ← v.decodeTable
  let library ← t.decode? (α := Name) `library
  let module ← t.decode? (α := Name) `module
  let package ← t.decode? (α := Name) `package
  return { library, module, package }

instance : DecodeToml Target := ⟨decodeTarget⟩

/-- Decode a `[metadata]` table entry into a `Metadata`. -/
def decodeMetadata (v : Value) : EDecodeM Metadata := do
  let t ← v.decodeTable
  let title ← t.decode? (α := String) `title
  let description ← t.decode? (α := String) `description
  let favicon ← t.decode? (α := String) `favicon
  return { title, description, favicon }

instance : DecodeToml Metadata := ⟨decodeMetadata⟩

/-- Decodes a TOML table into a `LiterateConfig`. -/
def decodeLiterateConfig (table : Table) : Except String LiterateConfig :=
  let decodeAction : DecodeM LiterateConfig := do
    let targets ← Table.tryDecodeD `targets (#[] : Array Target) table
    let exclude ← Table.tryDecodeD `exclude (#[] : Array Name) table
    let order ← Table.tryDecodeD `order (#[] : Array Name) table
    let orderChildren ← Table.tryDecodeD `order_children ({} : NameMap (Array Name)) table
    let landingPage ← table.tryDecode? (α := Name) `landing_page
    let hideCommands ← Table.tryDecodeD `hide_commands (#[] : Array Name) table
    let metadata ← Table.tryDecodeD `metadata ({} : Metadata) table
    let extraCss ← Table.tryDecodeD `extra_css (#[] : Array String) table
    let extraJs ← Table.tryDecodeD `extra_js (#[] : Array String) table
    let showDocstrings ← Table.tryDecodeD `show_docstrings (true : Bool) table
    let showDocstringsFor ← Table.tryDecodeD `show_docstrings_for (#[] : Array Name) table
    let hideDocstringsFor ← Table.tryDecodeD `hide_docstrings_for (#[] : Array Name) table
    let showOutput ← Table.tryDecodeD `show_output (#[`Lean.Parser.Command.eval, `Lean.Parser.Command.check, `Lean.Parser.Command.print, `Lean.reduceCmd] : Array Name) table
    let showImports ← Table.tryDecodeD `show_imports (true : Bool) table
    return { targets, exclude, order, orderChildren, landingPage,
             hideCommands, metadata, extraCss, extraJs,
             showDocstrings, showDocstringsFor, hideDocstringsFor,
             showOutput, showImports }
  match decodeAction #[] with
  | .ok config errors =>
    if errors.isEmpty then
      .ok config
    else
      let msgs := errors.map fun e => e.msg
      .error s!"Errors decoding literate.toml: {"\n".intercalate msgs.toList}"

/-- Parses a TOML string into a `LiterateConfig`. Returns default config for empty input. -/
def parseLiterateConfig (input : String) (source := "<string>") : IO LiterateConfig := do
  if input.trimAscii.isEmpty then
    return {}
  let ictx := Parser.mkInputContext input source
  match ← Lake.Toml.loadToml ictx |>.toBaseIO with
  | .ok table =>
    match decodeLiterateConfig table with
    | .ok config => return config
    | .error e => throw <| IO.userError e
  | .error log =>
    let msgs ← log.toList.mapM fun msg => msg.toString
    throw <| IO.userError s!"Failed to parse {source}:\n{"\n".intercalate msgs}"

/-- Loads and parses a `literate.toml` file. Returns default config if the file doesn't exist. -/
def loadLiterateConfig (path : System.FilePath) : IO LiterateConfig := do
  unless ← path.pathExists do
    return {}
  let input ← IO.FS.readFile path
  parseLiterateConfig input (source := path.toString)
