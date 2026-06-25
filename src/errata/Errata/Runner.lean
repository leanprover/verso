/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.TestM
public import Errata.IsTest
public import Errata.Report

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
  /-- The test declaration's name below its module. -/
  test : String
  /-- The test's own source range, used as the default failure location. -/
  location : Location
  /-- The action to run. -/
  run : TestM Unit

/-- Builds a test entry from any testable value. -/
def TestEntry.of {α} [IsTest α] (package moduleName test : String) (location : Location)
    (value : α) : TestEntry where
  package := package
  moduleName := moduleName
  test := test
  location := location
  run := IsTest.toTest value

/-- Runs a single test entry, collecting all of its results. -/
def runEntry (cfg : Context) (entry : TestEntry) : IO (Array Result) := do
  let log ← IO.mkRef (#[] : Array Result)
  let ctx := { cfg with
    package := entry.package, moduleName := entry.moduleName, test := entry.test,
    resultPath := #[], location := entry.location, log }
  let start ← IO.monoMsNow
  let (outcome, output) ← runCapturing ctx entry.run
  let stop ← IO.monoMsNow
  let dur := stop - start
  let logged ← log.get
  match outcome with
  | .error e => return logged.push { ctx.error (toString e) dur with output }
  | .ok (.error f) => return logged.push { ctx.fail f dur with output }
  | .ok (.ok ()) =>
    if logged.isEmpty then return #[ctx.pass dur] else return logged

/-- Runs all the test entries and collects their results. -/
def run (cfg : Context) (entries : Array TestEntry) : IO (Array Result) := do
  let mut all : Array Result := #[]
  for entry in entries do
    all := all ++ (← runEntry cfg entry)
  return all

/-- A base context with the given settings and a fresh, empty log. -/
def mkContext (verbosity : Verbosity := .silent) (updateGolden : Bool := false)
    (options : OptionMap := {}) (seed : Option Nat := none) : IO Context := do
  let log ← IO.mkRef (#[] : Array Result)
  let usedOptions ← IO.mkRef ({} : Std.HashSet String)
  return { verbosity, updateGolden, options, seed, log, usedOptions }

/-- The settings parsed from the runner's command line. -/
structure Options where
  /-- The reporting verbosity. -/
  verbosity : Verbosity := .silent
  /-- Rewrites golden expected files instead of comparing. -/
  updateGolden : Bool := false
  /-- The seed for property tests, for reproducing a failure. -/
  seed : Option Nat := none
  /-- Writes a JUnit XML report to this path. -/
  junitPath : Option String := none
  /-- Writes a JSON report to this path. -/
  jsonPath : Option String := none
  /-- Writes a Markdown report to this path. -/
  markdownPath : Option String := none
  /-- Project-specific options, as a multi-map so repeated options accumulate. -/
  options : OptionMap := {}
  /-- Prints usage information instead of running the tests. -/
  help : Bool := false

/--
{given}`name : String, value : String`

Parses arguments into {lean}`(name, value)` pairs.

A long option is {lit}`--name`, {lit}`--name=value`, or {lit}`--name value`. The {lit}`--name value`
form takes the next token as the value when that token is an ordinary argument; a token beginning with
{lit}`-` starts the next option instead, so a value beginning with {lit}`-` uses the {lit}`--name=value`
form. Short options bundle: {lit}`-xyz` is equivalent to {lit}`--x --y --z`, and the last may take a
following value. Any other argument is rejected.
-/
partial def rawOptions : List String → Except String (List (String × String))
  | [] => .ok []
  | arg :: rest =>
    if let some arg := arg.dropPrefix? "--" then
      match arg.copy.splitOn "=" with
      | [] => unreachable! -- `splitOn` always returns at least one element
      | [name] =>
        if name.isEmpty then .error s!"unexpected argument: {arg}"
        else match rest with
          | value :: rest' =>
            if value.startsWith "-" then (((name, "") :: ·)) <$> rawOptions rest
            else (((name, value) :: ·)) <$> rawOptions rest'
          | [] => .ok [(name, "")]
      | name :: valueParts =>
        if name.isEmpty then .error s!"unexpected argument: {arg}"
        else (((name, "=".intercalate valueParts) :: ·)) <$> rawOptions rest
    else if arg.startsWith "-" && arg.length > 1 then
      -- Expand bundled short flags: `-xyz` becomes `--x --y --z`.
      let expanded := (arg.drop 1).copy.toList.map (fun c => "--" ++ toString c)
      rawOptions (expanded ++ rest)
    else
      .error s!"unexpected argument: {arg}"

/-- Parses the runner's command-line arguments, peeling off known flags and keeping the rest as
project options. -/
def parseArgs (args : List String) : Except String Options := do
  let raw ← rawOptions args
  let mut opts : Options := {}
  for (name, value) in raw do
    match name with
    | "verbose" | "v" => opts := { opts with verbosity := opts.verbosity.increase }
    | "update-golden" => opts := { opts with updateGolden := true }
    | "seed" =>
      match value.toNat? with
      | some n => opts := { opts with seed := some n }
      | none => throw s!"--seed expects a natural number, got '{value}'"
    | "junit" =>
      if value.isEmpty then throw "--junit expects a path"
      opts := { opts with junitPath := some value }
    | "json" =>
      if value.isEmpty then throw "--json expects a path"
      opts := { opts with jsonPath := some value }
    | "markdown" =>
      if value.isEmpty then throw "--markdown expects a path"
      opts := { opts with markdownPath := some value }
    | "help" | "h" => opts := { opts with help := true }
    | _ =>
      let prev := opts.options.getD name #[]
      opts := { opts with options := opts.options.insert name (prev.push value) }
  return opts

/-- Usage information for the test runner, shown for {lit}`--help`. -/
def usage : String := include_str "usage.txt"

/-- The entry point the generated runner calls: parse arguments, run the tests, and report. -/
def runMain (entries : Array TestEntry) (args : List String) : IO UInt32 := do
  let opts ←
    match parseArgs args with
    | .ok opts => pure opts
    | .error msg =>
      IO.eprintln s!"error: {msg}"
      IO.eprintln usage
      return 1
  if opts.help then
    IO.println usage
    return 0
  let cfg ← mkContext (verbosity := opts.verbosity) (updateGolden := opts.updateGolden)
    (options := opts.options) (seed := opts.seed)
  let results ← run cfg entries
  if let some path := opts.junitPath then IO.FS.writeFile path (junitReport results)
  if let some path := opts.jsonPath then IO.FS.writeFile path (jsonReport results)
  if let some path := opts.markdownPath then IO.FS.writeFile path (markdownReport results)
  let failures ← humanReport opts.verbosity results
  -- Warn about options that were supplied but never read by any test (typos, removed flags).
  let used ← cfg.usedOptions.get
  let unused := opts.options.toList.filterMap fun (k, _) => if used.contains k then none else some k
  unless unused.isEmpty do
    IO.eprintln s!"warning: option(s) provided but never read: {", ".intercalate unused}"
  -- A process exit status keeps only its low 8 bits, so report a failing run as 1 rather than the
  -- count, which a multiple of 256 would otherwise wrap to 0.
  return if failures == 0 then 0 else 1
