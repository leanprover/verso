/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.TestM
public import Errata.IsTest
public import Errata.Report
public import Cli
import all Errata.FS

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
  /-- The test's docstring, rendered as Markdown, when it has one. -/
  docstring? : Option String := none
  /-- The action to run. -/
  run : TestM Unit

/-- Builds a test entry from any testable value. -/
def TestEntry.of {α} [IsTest α] (package moduleName test : String) (location : Location)
    (value : α) (docstring? : Option String := none) : TestEntry where
  package := package
  moduleName := moduleName
  test := test
  location := location
  docstring? := docstring?
  run := IsTest.toTest value

/-- Runs a single test entry, collecting all of its results. -/
def runEntry (cfg : Context) (entry : TestEntry) : IO (Array Result) := do
  let log ← IO.mkRef (#[] : Array Result)
  let ctx := { cfg with
    package := entry.package, moduleName := entry.moduleName, test := entry.test,
    resultPath := #[], location := entry.location, log, description? := entry.docstring?
  }
  let start ← IO.monoMsNow
  let (outcome, output) ← runCapturing ctx entry.run
  let stop ← IO.monoMsNow
  let dur := stop - start
  let logged ← log.get
  return match ctx.resultOfOutcome outcome output dur (!logged.isEmpty) with
    | some r => logged.push r
    | none => logged

/-- Runs all the test entries and collects their results. -/
def run (cfg : Context) (entries : Array TestEntry) : IO (Array Result) := do
  let mut all : Array Result := #[]
  for entry in entries do
    all := all ++ (← runEntry cfg entry)
  return all

/-- A base context with the given settings and a fresh, empty log. -/
def mkContext (updateGolden : Bool := false)
    (options : OptionMap := {}) (seed : Option Nat := none) : IO Context := do
  let log ← IO.mkRef (#[] : Array Result)
  let usedOptions ← IO.mkRef ({} : Std.HashSet String)
  let outputFailed ← IO.mkRef false
  return { updateGolden, options, seed, log, usedOptions, outputFailed }

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
  /-- Fails the run if warnings are logged. -/
  wfail : Bool := false
  /-- Project-specific options, as a multi-map so repeated options accumulate. -/
  options : OptionMap := {}

/--
The name of the driver script.

This must match its definition in `lakefile.lean`.
-/
def driverScript : String := "Errata.run"

/--
How the Errata driver is invoked.

This configuration is discovered from the workspace and used to inform users about how it should be
invoked.
-/
structure DriverConfig where
  /-- The workspace's root package. -/
  rootPackage : String
  /-- The root package's test driver setting, when it has one. -/
  testDriver : Option String
  /-- The package that defines the driver script. -/
  driverPackage : String
  /-- The package whose script a bare {lit}`lake run Errata.run` reaches, when there is one. -/
  bareScriptPackage : Option String

/--
How the Errata driver should be invoked. The driver script determines this from the Lake workspace's
configuration and incorporates it in the generated runner so it can guide users to the correct
invocation.
-/
structure Invocation where
  /-- The command that runs every test, such as {lit}`lake test`. -/
  run : String
  /--
  The command that the runner's own options follow, such as
  {lit}`lake test -- --test-options`.
  -/
  runner : String
deriving BEq, Repr

/--
Works out which command a user should type to run the tests.

The Errata driver is a Lake script named {lit}`Errata.run`. There are two ways that it might be
invoked:
 * Via {lit}`lake test`, when {lit}`Errata.run` is the test driver.
 * Explicitly via {lit}`lake run`, when it is not the test driver.

A script name written as {lit}`package/Errata.run` means the script in that specific package, and a
bare {lit}`Errata.run` is looked up without a package. The Lake parts of Errata determine the
simplest invocation that works in the current workspace, adding the package if some other package
also has a script named {lit}`Errata.run` that would be chosen instead.
-/
def Invocation.ofConfig (cfg : DriverConfig) : Invocation :=
  let qualified := s!"{cfg.driverPackage}/{driverScript}"
  let driver := cfg.testDriver.map fun d =>
    if d.contains '/' then d else s!"{cfg.rootPackage}/{d}"
  if driver == some qualified then { run := "lake test", runner := "lake test -- --test-options" }
  else
    let spec := if cfg.bareScriptPackage == some cfg.driverPackage then driverScript else qualified
    { run := s!"lake run {spec}", runner := s!"lake run {spec} --test-options" }

open Cli in
/--
The runner's command-line interface. The handler receives the parsed arguments. {name}`command` is
the command that the runner's options follow, shown in the usage header.
-/
def runnerCmd (command : String) (handler : Cli.Parsed → IO UInt32) : Cli.Cmd :=
  match cmd with
  | .init «meta» run subCmds extension? =>
    .init { «meta» with name := command } run subCmds extension?
where cmd := `[Cli|
    "errata" VIA handler;
    "Runs the discovered Errata tests."

    FLAGS:
      v, verbose;              "Also report passes, truncating each test's results."
      vv, "verbose-all";       "Report every result, without truncation."
      vvv, "verbose-docs";     "Report every result and every test's docstring."
      "update-golden";         "Rewrite golden expected files instead of comparing."
      seed : Nat;              "Seed property tests, to reproduce a failure."
      junit : String;          "Write a JUnit XML report to the given path."
      json : String;           "Write a JSON report to the given path."
      markdown : String;       "Write a Markdown report (for a CI job summary) to the given path."
      wfail;                   "Fail the run if warnings are logged."

    ARGS:
      ...testOption : String;  "Options for the tests themselves; see below."

    EXTENSIONS:
      longDescription "Options for the tests themselves go after a `--` separator, as \
        `--name value` or `--name=value`. Write a value that begins with `-` as `--name=value`."
  ]

/--
Parses the options passed through to the tests: {lit}`--name value` and {lit}`--name=value` pairs,
collected into a multi-map so repeated options accumulate. The {lit}`--name value` form takes the
next token as the value when that token does not begin with {lit}`-`; a value that does uses the
{lit}`--name=value` form. Any other token is rejected.
-/
partial def projectOptions (tokens : List String) : Except String OptionMap :=
  go {} tokens
where
  push (acc : OptionMap) (name value : String) : OptionMap :=
    acc.insert name ((acc.getD name #[]).push value)
  go (acc : OptionMap) : List String → Except String OptionMap
    | [] => .ok acc
    | tok :: rest =>
      match tok.dropPrefix? "--" with
      | none =>
        .error s!"unexpected argument '{tok}': test options are `--name value` or `--name=value`"
      | some name =>
        match name.copy.splitOn "=" with
        | [] => unreachable! -- `splitOn` always returns at least one element
        | [n] =>
          if n.isEmpty then .error s!"unexpected argument: {tok}"
          else match rest with
            | value :: rest' =>
              if value.startsWith "-" then go (push acc n "") rest
              else go (push acc n value) rest'
            | [] => .ok (push acc n "")
        | n :: valueParts =>
          if n.isEmpty then .error s!"unexpected argument: {tok}"
          else go (push acc n ("=".intercalate valueParts)) rest

/-- The value of a path-valued flag, when it is present; a present but empty path is an error. -/
private def pathFlag (p : Cli.Parsed) (name : String) : Except String (Option String) :=
  match p.flag? name with
  | none => .ok none
  | some f => if f.value.isEmpty then .error s!"--{name} expects a path" else .ok (some f.value)

/-- Interprets a parsed command line as runner settings. -/
def optionsOfParsed (p : Cli.Parsed) : Except String Options := do
  let verbosity : Verbosity :=
    if p.hasFlag "verbose-docs" then .superVerbose
    else if p.hasFlag "verbose-all" then .verbose
    else if p.hasFlag "verbose" then .quiet
    else .silent
  return {
    verbosity,
    updateGolden := p.hasFlag "update-golden",
    seed := p.flag? "seed" |>.map (·.as! Nat),
    junitPath := ← pathFlag p "junit",
    jsonPath := ← pathFlag p "json",
    markdownPath := ← pathFlag p "markdown",
    wfail := p.hasFlag "wfail",
    options := ← projectOptions (p.variableArgsAs! String).toList
  }

/--
Parses the runner's command line into settings: the declared flags, then any options for the tests
themselves after a {lit}`--` separator.
-/
def parseOptions (args : List String) : Except String Options :=
  match (runnerCmd "" fun _ => pure 0).parse args with
  | .error e => .error e.kind.msg
  | .ok (_, parsed) => optionsOfParsed parsed

/--
Parses the arguments, runs the tests, prints the results to the console, and writes any requested
report files.
-/
def runMain (invocation : Invocation) (entries : Array TestEntry) (args : List String) :
    IO UInt32 := do
  let cmd := runnerCmd invocation.runner fun parsed => do
    let opts ←
      match optionsOfParsed parsed with
      | .ok opts => pure opts
      | .error msg =>
        IO.eprintln s!"error: {msg}"
        return 1
    let cfg ← mkContext (updateGolden := opts.updateGolden)
      (options := opts.options) (seed := opts.seed)
    let results ← run cfg entries
    let writeReport (path? : Option String) (render : Array Result → String) : IO Unit := do
      if let some path := path? then
        writeFile path (render results)
    writeReport opts.junitPath junitReport
    writeReport opts.jsonPath jsonReport
    writeReport opts.markdownPath markdownReport
    let failures ← humanReport opts.verbosity results
    if entries.isEmpty then
      IO.eprintln "error: no tests were discovered"
      return 1
    -- Warn about options that were supplied but never read by any test (typos, removed flags).
    -- Under `--wfail`, the warning is an error and fails the run.
    let used ← cfg.usedOptions.get
    let unused := opts.options.toList.filterMap fun (k, _) => if used.contains k then none else some k
    unless unused.isEmpty do
      let level := if opts.wfail then "error" else "warning"
      IO.eprintln s!"{level}: option(s) provided but never read: {", ".intercalate unused}"
    -- A process exit status keeps only its low 8 bits, so report a failing run as 1 rather than the
    -- count, which a multiple of 256 would otherwise wrap to 0.
    if failures != 0 then return 1
    if opts.wfail && !unused.isEmpty then return 1
    return 0
  cmd.validate args

/--
Checks that the generated runner was started by the Errata driver, which passes {name}`driverFlag`
as the first argument. On success, the result is the remaining arguments. Otherwise, it is a message
that explains how to run the tests, and how to run the program directly anyway.
-/
def checkInvocation (driverFlag : String) (invocation : Invocation) (args : List String) :
    Except String (List String) :=
  match args with
  | flag :: rest =>
    if flag == driverFlag then .ok rest else .error notDriver
  | [] => .error notDriver
where
  notDriver :=
    s!"This program is generated and run by the Errata test driver, and is not meant to be run by \
      hand. To run the tests:\n  {invocation.run}\n\n\
      To run this program directly anyway, pass {driverFlag} as its first argument."

/--
The generated runner's entry point: checks that the Errata driver started the process by passing
{name}`driverFlag` first, then hands the remaining arguments to {name}`runMain`.
-/
def driverMain (driverFlag : String) (invocation : Invocation) (entries : Array TestEntry)
    (args : List String) : IO UInt32 := do
  match checkInvocation driverFlag invocation args with
  | .ok args => runMain invocation entries args
  | .error msg =>
    IO.eprintln msg
    return 1
