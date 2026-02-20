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
  runPlan (moduleListFile planOutputFile : String) (tomlFile : Option String) : IO UInt32 := do
    -- Read module list (one Name per line)
    let moduleListContents ← IO.FS.readFile moduleListFile
    let mut modules := moduleListContents.splitOn "\n"
      |>.filter (!·.isEmpty)
      |>.map String.toName

    -- Load config if TOML file provided
    let config ← match tomlFile with
      | some path => loadLiterateConfig path
      | none => pure ({} : LiterateConfig)

    -- Apply target filtering: if targets is non-empty, filter to matching modules
    if !config.targets.isEmpty then
      let targetModules := config.targets.filterMap fun t => t.module
      if !targetModules.isEmpty then
        modules := modules.filter fun m => targetModules.any fun t => t == m || t.isPrefixOf m

    -- Apply exclusion: remove modules with excluded prefixes
    if !config.exclude.isEmpty then
      modules := modules.filter fun m =>
        !config.exclude.any fun e => e.isPrefixOf m

    -- Write plan file
    let planContents := "\n".intercalate (modules.map Name.toString)
    IO.FS.writeFile planOutputFile (planContents ++ "\n")

    return 0
