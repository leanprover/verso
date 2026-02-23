/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoLiterate

open Lean
open VersoLiterate

/--
Checks whether `prefix` is a prefix of `name` (i.e. `name` is `prefix` or a child of it).
-/
def Name.isPrefixOf (prefix_ : Name) (name : Name) : Bool :=
  if prefix_ == name then true
  else match name with
  | .anonymous => false
  | .str parent _ => prefix_.isPrefixOf parent
  | .num parent _ => prefix_.isPrefixOf parent

/-- A module with its library membership. -/
structure LibModule where
  library : Name
  module : Name
deriving Repr

def main (args : List String) : IO UInt32 := do
  match args with
  | [moduleListFile, planOutputFile] =>
    runPlan moduleListFile planOutputFile none
  | [moduleListFile, planOutputFile, tomlFile] =>
    runPlan moduleListFile planOutputFile (some tomlFile)
  | _ =>
    IO.eprintln "Usage: verso-literate-plan <module-list-file> <plan-output-file> [<literate.toml>]"
    return 1
where
  /-- Parse a module list file. Each line is either:
      - `library_name\tmodule_name` (tab-separated, new format)
      - `module_name` (plain name, legacy format — library is set to anonymous) -/
  parseModuleList (contents : String) : List LibModule :=
    contents.splitOn "\n"
      |>.filter (!·.isEmpty)
      |>.map fun line =>
        match line.splitOn "\t" with
        | [lib, mod] => { library := lib.toName, module := mod.toName }
        | _ => { library := .anonymous, module := line.toName }

  /-- Check whether a target matches a module entry. A target matches if:
      - `target.module` matches (prefix of module name), or
      - `target.library` matches the module's library name
      When both are specified, both must match. -/
  targetMatches (target : Target) (entry : LibModule) : Bool :=
    let libOk := match target.library with
      | none => true
      | some lib => lib == entry.library
    let modOk := match target.module with
      | none => true
      | some mod => mod == entry.module || mod.isPrefixOf entry.module
    -- At least one of library or module must be specified for a meaningful match
    let hasConstraint := target.library.isSome || target.module.isSome
    hasConstraint && libOk && modOk

  runPlan (moduleListFile planOutputFile : String) (tomlFile : Option String) : IO UInt32 := do
    -- Read module list
    let moduleListContents ← IO.FS.readFile moduleListFile
    let mut entries := parseModuleList moduleListContents

    -- Load config if TOML file provided
    let config ← match tomlFile with
      | some path => loadLiterateConfig path
      | none => pure ({} : LiterateConfig)

    -- Apply target filtering: if targets is non-empty, filter to matching entries
    if !config.targets.isEmpty then
      entries := entries.filter fun entry =>
        config.targets.any fun target => targetMatches target entry

    -- Apply exclusion: remove modules with excluded prefixes
    if !config.exclude.isEmpty then
      entries := entries.filter fun entry =>
        !config.exclude.any fun e => e.isPrefixOf entry.module

    let modules := entries.map (·.module)

    -- Validate: empty module set
    if modules.isEmpty then
      IO.eprintln "Error: no modules to render (after applying targets and exclusions)"
      return 1

    -- Validate: landing_page must be in the included set
    if let some lp := config.landingPage then
      unless modules.any (· == lp) do
        IO.eprintln s!"Error: landing_page module '{lp}' is not in the included module set"
        return 1

    -- Validate: ordered modules should exist (warning only)
    for m in config.order do
      unless modules.any (· == m) do
        IO.eprintln s!"Warning: ordered module '{m}' does not exist in the module set"
    config.orderChildren.foldlM (init := ()) fun () parent children => do
      for m in children do
        unless modules.any (· == m) do
          IO.eprintln s!"Warning: ordered child module '{m}' (under '{parent}') does not exist in the module set"

    -- Write plan file
    let planContents := "\n".intercalate (modules.map Name.toString)
    IO.FS.writeFile planOutputFile (planContents ++ "\n")

    return 0
