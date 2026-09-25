/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.TestM
public import Errata.IsTest
public import Errata.Setting
public import Errata.Fixture

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/-- A fixture that a test takes, as a test executable lists it. -/
structure FixtureRef where
  /-- The fixture's name: its fully qualified declaration name. -/
  name : String
  /-- Whether the test uses the fixture alone among its users. -/
  exclusive : Bool
deriving Repr, Inhabited, BEq

/--
A fixture that a test executable runs the phases of: its identity, what it depends on, and the
action that runs a phase.
-/
structure FixtureEntry where
  /-- The fixture's name: its fully qualified declaration name. -/
  name : String
  /-- The fixture's own source range, used as the default failure location. -/
  location : Location := default
  /-- The fixture's docstring, rendered as Markdown, when it has one. -/
  docstring? : Option String := none
  /-- The settings that the fixture takes as parameters, in the order of its parameters. -/
  settings : Array SettingRef := #[]
  /-- The names of the fixtures that the fixture takes as parameters. -/
  fixtures : Array String := #[]
  /-- The number of hardware threads that the fixture's phases ask for, when it asks. -/
  threads? : Option Nat := none
  /--
  Runs a phase, given the settings and the fixtures' values as name and value pairs, the phase, and
  the fixture's own value when the phase receives one. The result is the value that a setup
  produced, as a string.
  -/
  run : Array (String × String) → Array (String × String) → FixturePhase → Option String →
    FixtureM (Option String)

/-- A test to run: its identity, what it depends on, and the action that produces its results. -/
structure TestEntry where
  /-- The package that defines the test. -/
  package : String
  /-- The module that defines the test, as a dotted name. -/
  moduleName : String
  /-- The test's name: its fully qualified declaration name. -/
  name : String
  /-- The components of the test's name, for nesting in reports. -/
  path : Array String
  /-- The test's own source range, used as the default failure location. -/
  location : Location
  /-- The test's docstring, rendered as Markdown, when it has one. -/
  docstring? : Option String := none
  /-- The test's tags. -/
  tags : Array String := #[]
  /-- The settings that the test takes as parameters, in the order of its parameters. -/
  settings : Array SettingRef := #[]
  /-- The fixtures that the test takes as parameters, in the order of its parameters. -/
  fixtures : Array FixtureRef := #[]
  /--
  The action to run, given the settings and then the fixtures' values as name and value pairs. It
  parses the values of the settings and fixtures that the test takes and applies the test to them.
  -/
  run : Array (String × String) → Array (String × String) → TestM Unit

/--
Builds a test entry from any testable value, which takes no settings or fixtures. The name's
components are its path, split at dots.
-/
def TestEntry.of {α} [IsTest α] (package moduleName name : String) (location : Location)
    (value : α) (docstring? : Option String := none) : TestEntry where
  package := package
  moduleName := moduleName
  name := name
  path := if name.isEmpty then #[] else (name.splitOn ".").toArray
  location := location
  docstring? := docstring?
  run := fun _ _ => IsTest.toTest value

/--
Runs a single test entry with the given settings and fixtures' values, as name and value pairs,
collecting all of its results.
-/
def runEntry (cfg : TestContext) (entry : TestEntry) (settings : Array (String × String) := #[])
    (fixtures : Array (String × String) := #[]) : IO (Array Result) := do
  let log ← IO.mkRef (#[] : Array Result)
  let insideMs ← IO.mkRef 0
  let ctx := { cfg with
    test := entry.name, path := entry.path,
    resultPath := #[], location := entry.location, log, insideMs,
    description? := entry.docstring?
  }
  let start ← IO.monoMsNow
  let (outcome, output) ← runCapturing ctx (entry.run settings fixtures)
  let stop ← IO.monoMsNow
  let dur := stop - start
  let logged ← log.get
  return #[ctx.resultOfOutcome outcome output dur (← insideMs.get) logged] ++ logged

/-- A base context with a fresh, empty log. -/
def mkContext (updateGolden : Bool := false) : IO TestContext := do
  let log ← IO.mkRef (#[] : Array Result)
  let outputFailed ← IO.mkRef false
  let watchFailed ← IO.mkRef false
  let insideMs ← IO.mkRef 0
  return { updateGolden, log, outputFailed, watchFailed, insideMs }
