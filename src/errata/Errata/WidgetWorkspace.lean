/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
What the run-test widget's server reads from the workspace, and how it invokes the driver: the
package whose driver script it runs, the arguments of a run, the library that holds a test's module,
and the profiles that a test's runs can use, with the values that each gives the test's settings.
-/
module

public import Errata.RunnerConfig
public import Errata.Resolution
public import Errata.Harness

public section

set_option linter.missingDocs true
set_option doc.verso true

open Lean (Json)
open Errata.Runner (SourcedFilter)

namespace Errata.Widget

/-- Whether the path {name}`dir` is {name}`path` or a directory above it. -/
def isPathPrefix (dir path : System.FilePath) : Bool :=
  let d := dir.components.filter (!·.isEmpty)
  let p := path.components.filter (!·.isEmpty)
  d.length ≤ p.length && p.take d.length == d

/--
The packages of the workspace at {name}`workspace`, from its {lit}`lake-manifest.json`, each with a
directory that holds its build: for the root package, its own build directory in its Lake directory,
and for each other package, its directory, which the manifest names or which is its clone in the
manifest's packages directory. Directories that are absent on disk are left out, and the rest are
resolved to real paths.
-/
def manifestPackages (workspace : System.FilePath) : IO (Array (String × System.FilePath)) := do
  let manifest ← try Runner.readJsonFile (workspace / "lake-manifest.json") catch _ => return #[]
  let packagesDir : System.FilePath :=
    (manifest.getObjValAs? String "packagesDir").toOption.getD ".lake/packages"
  let lakeDir : System.FilePath := (manifest.getObjValAs? String "lakeDir").toOption.getD ".lake"
  let mut out := #[]
  if let .ok root := manifest.getObjValAs? String "name" then
    out := out.push (root, workspace / lakeDir / "build")
  for entry in (manifest.getObjValAs? (Array Json) "packages").toOption.getD #[] do
    let some name := (entry.getObjValAs? String "name").toOption | continue
    let dir : System.FilePath := match (entry.getObjValAs? String "dir").toOption with
      | some d => workspace / d
      | none =>
        let clone := workspace / packagesDir / name
        match (entry.getObjValAs? String "subDir").toOption with
        | some sub => clone / sub
        | none => clone
    out := out.push (name, dir)
  out.filterMapM fun (name, dir) => do
    try return some (name, ← IO.FS.realPath dir) catch _ => return none

/--
The script with which Lake runs Errata's driver in the workspace at {name}`workspace`, qualified by
the package that defines it, such as {lit}`verso/Errata.run`, so that a script of the same name in
the root package leaves it in place. The package is the one whose directory, as
{name}`manifestPackages` gives it, holds the first {lit}`Errata.olean` on the search path
{name}`leanPath`, the deepest when directories nest: the root package when the file lies in the
root's own build directory, as it does when Errata is a library of the root package. When no
package holds it, the script is named {lit}`Errata.run` alone.
-/
def driverScript (leanPath : List System.FilePath) (workspace : System.FilePath) : IO String := do
  let some oleanDir ← leanPath.findM? fun dir => (dir / "Errata.olean").pathExists
    | return "Errata.run"
  let oleanDir ← IO.FS.realPath oleanDir
  let holders := (← manifestPackages workspace).filter (isPathPrefix ·.2 oleanDir)
  let deepest := holders.foldl (init := none) fun best? (name, dir) =>
    match best? with
    | some (_, bestDir) =>
      if dir.components.length > bestDir.components.length then some (name, dir) else best?
    | none => some (name, dir)
  match deepest with
  | some (name, _) => return s!"{name}/Errata.run"
  | none => return "Errata.run"

/-- What a run of one test asks of the driver. -/
structure DriverRequest where
  /-- The module that defines the test. -/
  module : Lean.Name
  /-- The test's name, as its test executable names it. -/
  test : String
  /-- The file for the runner's events. -/
  eventsPath : System.FilePath := ""
  /-- The seed for property tests, when the widget gives one. -/
  seed? : Option Nat := none
  /-- Whether the test takes the seed setting, which then receives the seed. -/
  takesSeed : Bool := false
  /-- Values for the test's settings. -/
  settings : Array (String × String) := #[]
  /-- The driver's script, qualified by its package, as {name}`driverScript` names it. -/
  script : String := "Errata.run"
  /-- The profile of the run, when the widget names one. -/
  profile? : Option String := none

/--
The arguments with which {lit}`lake` runs the driver for one test. The driver is the request's
script, named with the package that defines it. The arguments name the test's module, which runs
through the interpreted product of the Lean harness, a filter that selects the test by its name with
the profile's default filter set aside, since the run is of that one test, the file for the runner's
events, the profile, the seed, and the settings' values. If the test takes the seed setting, the
seed is that setting's value; otherwise the runner receives it as the run's seed.
-/
def driverArgs (r : DriverRequest) : Array String :=
  let seed := match r.seed? with
    | some n =>
      if r.takesSeed then #["--set", s!"{Runner.seedSetting}={n}"] else #["--seed", toString n]
    | none => #[]
  let profile := match r.profile? with
    | some p => #["-P", p]
    | none => #[]
  #["script", "run", r.script, "run", "-E", s!"name(={Filter.escapeText r.test})",
    "--ignore-default-filter", "--interpreted", r.module.toString, "--events",
    r.eventsPath.toString] ++ profile ++ seed ++
    r.settings.flatMap fun (k, v) => #["--set", s!"{k}={v}"]

/-- A library of the workspace's root package, with the roots and globs that give its modules. -/
structure LibraryModules where
  /-- The library's name, which is also its test executable's. -/
  name : String
  /-- The library's root modules. -/
  roots : Array Lean.Name := #[]
  /--
  The library's globs: a module, the modules below one ({lit}`M.+`), or a module and those below it
  ({lit}`M.*`), each with the module and whether the glob takes the module itself and those below
  it.
  -/
  globs : Array (Lean.Name × Bool × Bool) := #[]
deriving Repr, Inhabited

/-- Reads a glob in Lake's notation: {lit}`M`, {lit}`M.+`, or {lit}`M.*`. -/
def LibraryModules.globOf (text : String) : Lean.Name × Bool × Bool :=
  if let some m := text.dropSuffix? ".+" then (Harness.moduleNameOf m.copy, false, true)
  else if let some m := text.dropSuffix? ".*" then (Harness.moduleNameOf m.copy, true, true)
  else (Harness.moduleNameOf text, true, false)

/-- Whether the glob takes the module. -/
def LibraryModules.globTakes (glob : Lean.Name × Bool × Bool) (mod : Lean.Name) : Bool :=
  let (base, itself, below) := glob
  (itself && base == mod) || (below && base.isPrefixOf mod && base != mod)

/--
Whether the library builds the module, as Lake decides it: a glob takes the module, or a root that a
glob takes is the module or a module above it.
-/
def LibraryModules.holds (lib : LibraryModules) (mod : Lean.Name) : Bool :=
  lib.globs.any (globTakes · mod) ||
    lib.roots.any fun root => root.isPrefixOf mod && lib.globs.any (globTakes · root)

/-- The libraries that {lit}`workspace.json` records under {lit}`libraries`. -/
def LibraryModules.ofWorkspaceJson (j : Json) : Array LibraryModules :=
  ((j.getObjValAs? (Array Json) "libraries").toOption.getD #[]).filterMap fun lib => do
    let name ← (lib.getObjValAs? String "name").toOption
    let roots := (lib.getObjValAs? (Array String) "roots").toOption.getD #[]
    let globs := (lib.getObjValAs? (Array String) "globs").toOption.getD #[]
    return { name, roots := roots.map Harness.moduleNameOf
             globs := globs.map LibraryModules.globOf }

/--
The library among {name}`libs` that holds the module {name}`mod`: the last that builds it, as Lake
finds a module's library.
-/
def libraryOf (libs : Array LibraryModules) (mod : Lean.Name) : Option String :=
  (libs.reverse.find? (·.holds mod)).map (·.name)

/-- A profile that a test's runs can use, with the values it gives the test's settings. -/
structure ProfileChoice where
  /-- The profile's name. -/
  name : String
  /-- Whether the profile is the fallback, offered when no default filter selects the test. -/
  fallback : Bool := false
  /--
  The values that the test receives from the profile: for each setting, the first override that
  matches the test and gives it a value, or else the profile.
  -/
  values : Array (String × String) := #[]
deriving Repr, Inhabited, BEq

/--
The values that the profile gives the test {name}`record`: for each setting that the profile or one
of its overrides gives a value, the first override that matches the test and gives it one, or else
the profile's value. {name}`dflt` is whether the default filter selects the test, which
{lit}`default()` stands for in the overrides' filters. Overrides whose filters cannot be read give
nothing.
-/
def profileValues (profile : Runner.Profile) (record : Filter.Record) (dflt : Bool) :
    Array (String × String) := Id.run do
  let matching := profile.overrides.filter fun o =>
    match SourcedFilter.parse o.filter.text o.filter.source with
    | .ok f => f.expr.eval record dflt
    | .error _ => false
  let mut names : Array String := #[]
  for (k, _) in profile.settings ++ matching.flatMap (·.settings) do
    unless names.contains k do names := names.push k
  return names.filterMap fun k =>
    ((matching.findSome? fun o => o.settings.find? (·.1 == k)) <|>
      profile.settings.find? (·.1 == k)).map (k, ·.2)

/--
The profiles of {name}`config` that a run of the test {name}`record` can use: those whose default
filter selects the test, or that have none, the {lit}`default` profile first and the others in the
configuration's order. When none selects the test, the one choice is the {lit}`default` profile,
marked as the fallback. Default filters that cannot be read select nothing.
-/
def profileChoices (config : Runner.Config) (record : Filter.Record) : Array ProfileChoice :=
  let names := #["default"] ++ config.profileNames.filter (· != "default")
  let judged := names.filterMap fun name => do
    let profile ← config.profile? name
    let selects := match profile.defaultFilter? <|> config.defaultFilter? with
      | none => true
      | some f => match SourcedFilter.parse f.text f.source with
        | .ok f => f.expr.eval record
        | .error _ => false
    return (profile, selects)
  let offered := judged.filterMap fun (p, selects) =>
    if selects then some { name := p.name, values := profileValues p record true } else none
  if offered.isEmpty then
    let dflt := (config.profile? "default").getD { name := "default" }
    #[{ name := "default", fallback := true, values := profileValues dflt record false }]
  else offered

end Errata.Widget
