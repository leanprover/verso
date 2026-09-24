/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.TestM
public import Errata.IsTest
public import Errata.Setting

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

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
  /--
  The action to run, given the settings as name and value pairs. It parses the values of the
  settings that the test takes and applies the test to them.
  -/
  run : Array (String × String) → TestM Unit

/--
Builds a test entry from any testable value, which takes no settings. The name's components are its
path, split at dots.
-/
def TestEntry.of {α} [IsTest α] (package moduleName name : String) (location : Location)
    (value : α) (docstring? : Option String := none) : TestEntry where
  package := package
  moduleName := moduleName
  name := name
  path := if name.isEmpty then #[] else (name.splitOn ".").toArray
  location := location
  docstring? := docstring?
  run := fun _ => IsTest.toTest value

/--
Runs a single test entry with the given settings, as name and value pairs, collecting all of its
results.
-/
def runEntry (cfg : TestContext) (entry : TestEntry) (settings : Array (String × String) := #[]) :
    IO (Array Result) := do
  let log ← IO.mkRef (#[] : Array Result)
  let insideMs ← IO.mkRef 0
  let ctx := { cfg with
    test := entry.name, path := entry.path,
    resultPath := #[], location := entry.location, log, insideMs,
    description? := entry.docstring?
  }
  let start ← IO.monoMsNow
  let (outcome, output) ← runCapturing ctx (entry.run settings)
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
