/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.TestM
public import Errata.IsTest

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/-- A test to run: its identity and the action that produces its results. -/
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
  /-- The action to run. -/
  run : TestM Unit

/--
Builds a test entry from any testable value. The name's components are its path, split at dots.
-/
def TestEntry.of {α} [IsTest α] (package moduleName name : String) (location : Location)
    (value : α) (docstring? : Option String := none) : TestEntry where
  package := package
  moduleName := moduleName
  name := name
  path := if name.isEmpty then #[] else (name.splitOn ".").toArray
  location := location
  docstring? := docstring?
  run := IsTest.toTest value

/-- Runs a single test entry, collecting all of its results. -/
def runEntry (cfg : Context) (entry : TestEntry) : IO (Array Result) := do
  let log ← IO.mkRef (#[] : Array Result)
  let insideMs ← IO.mkRef 0
  let ctx := { cfg with
    test := entry.name, path := entry.path,
    resultPath := #[], location := entry.location, log, insideMs,
    description? := entry.docstring?
  }
  let start ← IO.monoMsNow
  let (outcome, output) ← runCapturing ctx entry.run
  let stop ← IO.monoMsNow
  let dur := stop - start
  let logged ← log.get
  return #[ctx.resultOfOutcome outcome output dur (← insideMs.get) logged] ++ logged

/-- Runs all the test entries in this process, one after another, and collects their results. -/
def run (cfg : Context) (entries : Array TestEntry) : IO (Array Result) := do
  let mut all : Array Result := #[]
  for entry in entries do
    all := all ++ (← runEntry cfg entry)
  return all

/--
A base context with the given settings and a fresh, empty log. Without a seed for property tests,
one is generated using the default Lean RNG.
-/
def mkContext (updateGolden : Bool := false)
    (options : OptionMap := {}) (seed : Option Nat := none) (ignorePanics : Bool := false) :
    IO Context := do
  let seed ←
    match seed with
    | some seed => pure seed
    | none => IO.rand 0 (2 ^ 32 - 1)
  let log ← IO.mkRef (#[] : Array Result)
  let usedOptions ← IO.mkRef ({} : Std.HashSet String)
  let outputFailed ← IO.mkRef false
  let watchFailed ← IO.mkRef false
  let insideMs ← IO.mkRef 0
  return {
    updateGolden, options, seed, ignorePanics, log, usedOptions, outputFailed, watchFailed, insideMs
  }
