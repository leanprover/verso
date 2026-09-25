/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The inventory of test modules as their `.olean` files record it, which the interpreted product of
the Lean harness lists with no import.
-/
module

public import Errata.Runner
public import Errata.TestRegistry
public import Lean.Environment
public import Lean.Util.Path

open Lean

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata.OleanListing

/--
The settings that a test or fixture takes, each with its docstring as its description and its
declared default as {lit}`@[setting]` recorded it.
-/
def settingRefsOf (uses : Array SettingUse) : Array SettingRef :=
  uses.map fun use => {
    name := settingNameOf use.decl, optional := use.optional
    description? := use.description?, default? := use.default? }

/--
A recorded test of the module {name}`module` at {name}`location`, as {lit}`getAllTests%` lists it,
with the settings as {name}`settingRefsOf` gives them: each fixture is exclusive or shared, and the
threads are those that the test asks for.
-/
def testInfoOf (module : Name) (test : TestDecl) (location : Location) : TestInfo :=
  let userName := privateToUserName test.name
  { package := "", moduleName := module.toString
    name := userName.toString
    path := userName.components.map (·.toString (escape := false)) |>.toArray
    location, docstring? := test.docstring?, tags := test.tags
    settings := settingRefsOf test.settings
    fixtures := test.fixtures.map fun use =>
      { name := settingNameOf use.decl, exclusive := use.exclusive }
    threads? := test.threads? }

/-- A recorded fixture, as {lit}`getAllFixtures%` lists it, with its settings' recorded defaults. -/
def fixtureInfoOf (f : FixtureDecl) : FixtureInfo :=
  { name := settingNameOf f.name, docstring? := f.docstring?
    settings := settingRefsOf f.settings, fixtures := f.fixtures.map settingNameOf
    threads? := f.threads? }

/--
The tests that the module's {lit}`.olean` file records, read from the file's entries of
{name}`testExt`, which is found through the search path. The file's memory stays mapped for the
rest of the process, since the records point into it.
-/
unsafe def recordedTests (module : Name) : IO (Array TestDecl) := do
  let (data, _) ← readModuleData (← findOLean module)
  match data.entries.find? (·.1 == testExt.name) with
  | some (_, entries) => return unsafeCast entries
  | none => return #[]

/--
The inventory of the tests that the modules in {name}`modules` record, each module read once, and of
the fixtures that the tests reach, read from the modules' {lit}`.olean` files with no import: each
test as {name}`testInfoOf` gives it at the declaration range that the file records. The result is
{lean}`none` when a setting that a test or one of its fixtures takes has a default that
{lit}`@[setting]` could not evaluate, or when the file records no range for a test, since an import
finds both.

The files are read as they are on disk. The driver builds the modules before a run lists them; a
module edited after its last build lists what its build recorded.
-/
unsafe def listed? (modules : Array Name) : IO (Option (Array TestInfo × Array FixtureInfo)) := do
  let mut seen : NameSet := {}
  let mut tests := #[]
  let mut fixtures := #[]
  let mut fixtureNames : NameSet := {}
  for module in modules do
    if seen.contains module then continue
    seen := seen.insert module
    for test in ← recordedTests module do
      let uses := test.settings ++ test.reachedFixtures.flatMap (·.settings)
      unless uses.all (·.defaultEvaluated) do return none
      let some location := test.location? | return none
      tests := tests.push (testInfoOf module test location)
      for f in test.reachedFixtures do
        unless fixtureNames.contains f.name do
          fixtureNames := fixtureNames.insert f.name
          fixtures := fixtures.push (fixtureInfoOf f)
  return some (tests, fixtures)

end Errata.OleanListing
