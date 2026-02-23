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

/-- Per-module configuration overrides from `[modules."Foo.Bar"]` in `literate.toml`. -/
structure ModuleConfig where
  title : Option String := none
  url : Option String := none
  hideCommands : Option (Array String) := none
  showOutput : Option (Array String) := none
  showImports : Option Bool := none
  showDocstrings : Option Bool := none
  showDocstringsFor : Option (Array Name) := none
  hideDocstringsFor : Option (Array Name) := none
deriving Repr, BEq, Inhabited

/-- The merged result of resolving per-module config against global defaults. -/
structure ResolvedConfig where
  hideCommands : Array String
  showOutput : Array String
  showImports : Bool
  showDocstrings : Bool
  showDocstringsFor : Array Name
  hideDocstringsFor : Array Name
  title : Option String := none
  url : Option String := none
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
  /-- Command keyword patterns to hide (e.g. `"import"`, `"set_option"`, `"#eval"`).
      Each pattern is a space-separated sequence of keyword tokens that must appear
      at the start of the command's highlighted code. Matching is done on keyword
      token content, so `"#eval"` matches both `#eval` and `#eval in`. -/
  hideCommands : Array String := #[]
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
  /-- Command keyword patterns whose output (info messages) should be displayed as a
      separate block (e.g. `"#eval"`, `"#check"`, `"#print"`). Matching works the same
      way as `hideCommands`. -/
  showOutput : Array String := #["#eval", "#check", "#print", "#reduce"]
  /-- Whether to show the collapsible imports list on each page. -/
  showImports : Bool := true
  /-- Theme CSS variable overrides (key → value). Keys use `_` for `-`. -/
  theme : Std.TreeMap String String compare := {}
  /-- Dark mode theme CSS variable overrides (key → value). -/
  themeDark : Std.TreeMap String String compare := {}
  /-- Per-module configuration overrides keyed by module name. -/
  modules : NameMap ModuleConfig := {}
deriving Repr, Inhabited

/-- Decodes a `[[targets]]` table entry into a `Target`. -/
def decodeTarget (v : Value) : EDecodeM Target := do
  let t ← v.decodeTable
  let library ← t.decode? (α := Name) `library
  let module ← t.decode? (α := Name) `module
  let package ← t.decode? (α := Name) `package
  return { library, module, package }

instance : DecodeToml Target := ⟨decodeTarget⟩

/-- Decodes a `[metadata]` table entry into a `Metadata`. -/
def decodeMetadata (v : Value) : EDecodeM Metadata := do
  let t ← v.decodeTable
  let title ← t.decode? (α := String) `title
  let description ← t.decode? (α := String) `description
  let favicon ← t.decode? (α := String) `favicon
  return { title, description, favicon }

instance : DecodeToml Metadata := ⟨decodeMetadata⟩

/-- Decodes a `[modules."Foo.Bar"]` table entry into a `ModuleConfig`. -/
def decodeModuleConfig (v : Value) : EDecodeM ModuleConfig := do
  let t ← v.decodeTable
  let title ← t.decode? (α := String) `title
  let url ← t.decode? (α := String) `url
  let hideCommands ← t.decode? (α := Array String) `hide_commands
  let showOutput ← t.decode? (α := Array String) `show_output
  let showImports ← t.decode? (α := Bool) `show_imports
  let showDocstrings ← t.decode? (α := Bool) `show_docstrings
  let showDocstringsFor ← t.decode? (α := Array Name) `show_docstrings_for
  let hideDocstringsFor ← t.decode? (α := Array Name) `hide_docstrings_for
  return { title, url, hideCommands, showOutput, showImports,
           showDocstrings, showDocstringsFor, hideDocstringsFor }

instance : DecodeToml ModuleConfig := ⟨decodeModuleConfig⟩

/-- Decodes a `[modules]` table into a `NameMap ModuleConfig`.
    TOML keys like `"Foo.Bar"` produce single-component Names, so we
    convert them to proper dotted Lean Names using `String.toName`. -/
def decodeModulesMap (table : Table) : DecodeM (NameMap ModuleConfig) := do
  match table.find? `modules with
  | none => return {}
  | some modulesVal =>
    match modulesVal with
    | .table' _ modulesTable =>
      let mut result : NameMap ModuleConfig := {}
      for (k, v) in modulesTable.items do
        let modName := (k.toString (escape := false)).toName
        match decodeModuleConfig v #[] with
        | .ok mc errors =>
          unless errors.isEmpty do modify (· ++ errors)
          result := result.insert modName mc
        | .error () errors => modify (· ++ errors)
      return result
    | _ => return {}

/-- Decodes a `[theme]` table into light and dark CSS variable maps.
    Sub-keys that are strings become light-mode variables; the `dark` sub-table
    provides dark-mode overrides. -/
def decodeThemeTable (themeTable : Table) : Std.TreeMap String String compare × Std.TreeMap String String compare :=
  let (light, dark) := themeTable.items.foldl (init := ({}, {})) fun (light, dark) (k, v) =>
    if k == `dark then
      match v with
      | .table' _ darkTable =>
        let dark := darkTable.items.foldl (init := dark) fun dark (dk, dv) =>
          match dv with
          | .string _ s => dark.insert dk.toString s
          | _ => dark
        (light, dark)
      | _ => (light, dark)
    else
      match v with
      | .string _ s => (light.insert k.toString s, dark)
      | _ => (light, dark)
  (light, dark)

def decodeTheme (table : Table) : DecodeM (Std.TreeMap String String compare × Std.TreeMap String String compare) := do
  match table.find? `theme with
  | none => return ({}, {})
  | some themeVal =>
    match themeVal with
    | .table' _ themeTable => return decodeThemeTable themeTable
    | _ => return ({}, {})

/-- Resolve per-module configuration for a given module name by finding the
    longest-prefix match in `modules` and merging with global defaults.
    Module-level settings override global settings. -/
def LiterateConfig.resolveForModule (config : LiterateConfig) (modName : Name) : ResolvedConfig :=
  let bestMatch := config.modules.foldl (init := (Name.anonymous, none)) fun (bestName, bestCfg) k v =>
    if k.isPrefixOf modName && k.components.length > bestName.components.length then
      (k, some v)
    else
      (bestName, bestCfg)
  match bestMatch.2 with
  | none =>
    { hideCommands := config.hideCommands
      showOutput := config.showOutput
      showImports := config.showImports
      showDocstrings := config.showDocstrings
      showDocstringsFor := config.showDocstringsFor
      hideDocstringsFor := config.hideDocstringsFor }
  | some mc =>
    { hideCommands := mc.hideCommands.getD config.hideCommands
      showOutput := mc.showOutput.getD config.showOutput
      showImports := mc.showImports.getD config.showImports
      showDocstrings := mc.showDocstrings.getD config.showDocstrings
      showDocstringsFor := mc.showDocstringsFor.getD config.showDocstringsFor
      hideDocstringsFor := mc.hideDocstringsFor.getD config.hideDocstringsFor
      title := mc.title
      url := mc.url }

/-- Decodes a TOML table into a `LiterateConfig`. -/
def decodeLiterateConfig (table : Table) : Except String LiterateConfig :=
  let decodeAction : DecodeM LiterateConfig := do
    let targets ← Table.tryDecodeD `targets (#[] : Array Target) table
    let exclude ← Table.tryDecodeD `exclude (#[] : Array Name) table
    let order ← Table.tryDecodeD `order (#[] : Array Name) table
    let orderChildren ← Table.tryDecodeD `order_children ({} : NameMap (Array Name)) table
    let landingPage ← table.tryDecode? (α := Name) `landing_page
    let hideCommands ← Table.tryDecodeD `hide_commands (#[] : Array String) table
    let metadata ← Table.tryDecodeD `metadata ({} : Metadata) table
    let extraCss ← Table.tryDecodeD `extra_css (#[] : Array String) table
    let extraJs ← Table.tryDecodeD `extra_js (#[] : Array String) table
    let showDocstrings ← Table.tryDecodeD `show_docstrings (true : Bool) table
    let showDocstringsFor ← Table.tryDecodeD `show_docstrings_for (#[] : Array Name) table
    let hideDocstringsFor ← Table.tryDecodeD `hide_docstrings_for (#[] : Array Name) table
    let showOutput ← Table.tryDecodeD `show_output (#["#eval", "#check", "#print", "#reduce"] : Array String) table
    let showImports ← Table.tryDecodeD `show_imports (true : Bool) table
    let (theme, themeDark) ← decodeTheme table
    let modules ← decodeModulesMap table
    return { targets, exclude, order, orderChildren, landingPage,
             hideCommands, metadata, extraCss, extraJs,
             showDocstrings, showDocstringsFor, hideDocstringsFor,
             showOutput, showImports, theme, themeDark, modules }
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
