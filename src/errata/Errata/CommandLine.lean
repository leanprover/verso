/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The runner's command line, in the shape of `cargo nextest`'s where the two tools have the same
feature: a command, `run` or `list`, then options and name filters, with more name filters after
`--`. This module also holds the exit codes that the runner and the driver end with.
-/
module

public import Errata.Result

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata.Runner

/-- What the runner is asked to do. -/
inductive Command where
  /-- Run the selected tests. -/
  | run
  /-- List the selected tests and run nothing. -/
  | list
deriving Repr, Inhabited, DecidableEq

/-- The command as the command line writes it. -/
def Command.name : Command → String
  | .run => "run"
  | .list => "list"

/-- What a run that selects no test ends with. -/
inductive NoTests where
  /-- An error, and the exit code {lit}`4`. -/
  | fail
  /-- A warning, and success. -/
  | warn
  /-- Success. -/
  | pass
deriving Repr, Inhabited, DecidableEq

/-- When the human-readable output is colored. -/
inductive ColorChoice where
  /-- When standard output is a terminal, unless the environment says otherwise. -/
  | auto
  /-- Always. -/
  | always
  /-- Never. -/
  | never
deriving Repr, Inhabited, DecidableEq

/-- The format of what the {lit}`list` command prints. -/
inductive MessageFormat where
  /-- Each test executable's name, then its tests, indented. -/
  | human
  /-- One line per test: the executable, the name, the file and line, and the tags. -/
  | oneline
  /-- The inventory as JSON on one line, with what each test receives. -/
  | json
  /-- The inventory as indented JSON, with what each test receives. -/
  | jsonPretty
deriving Repr, Inhabited, DecidableEq

/-!
The exit codes of the runner and the driver. Where a code has a meaning that {lit}`cargo nextest`
also has, the value is nextest's ({lit}`NextestExitCode` in {lit}`nextest-metadata`).
-/
namespace ExitCode

/-- Every selected test passed, or a listing succeeded. -/
def ok : UInt32 := 0

/-- A cancelled run, or a failure without a code of its own. -/
def other : UInt32 := 1

/-- The command line could not be read. The value is the one that nextest's argument parser uses. -/
def usage : UInt32 := 2

/-- The run selected no test, under {lit}`--no-tests fail` (nextest's {lit}`NO_TESTS_RUN`). -/
def noTestsRun : UInt32 := 4

/--
A filter on the command line has a syntax error. The value is nextest's {lit}`INVALID_FILTERSET`,
named after nextest's term for a filter.
-/
def invalidFilter : UInt32 := 94

/--
The configuration of the run is wrong: {lit}`errata.toml`, the profile, a setting's value, or a
target that a setting needs (nextest's {lit}`SETUP_ERROR`).
-/
def setupError : UInt32 := 96

/-- A test did not pass, or an issue with the run is an error (nextest's {lit}`TEST_RUN_FAILED`). -/
def testRunFailed : UInt32 := 100

/-- A test executable or a needed target could not be built (nextest's {lit}`BUILD_FAILED`). -/
def buildFailed : UInt32 := 101

/-- A test executable could not list its tests (nextest's {lit}`TEST_LIST_CREATION_FAILED`). -/
def listFailed : UInt32 := 104

end ExitCode

/-- The runner's options, from its command line. -/
structure Options where
  /-- The path of the configuration file that {lit}`errata-config` writes. -/
  configPath : String := ""
  /-- The path of the workspace's configuration file that the driver writes. -/
  workspacePath : String := ""
  /-- What to do. -/
  command : Command := .run
  /-- The reporting verbosity; for {lit}`list`, anything above silent shows the settings. -/
  verbosity : Verbosity := .silent
  /-- Passes {lit}`setting:Errata.updateGolden=true` to every test. -/
  updateGolden : Bool := false
  /-- The run's seed, from which each test's seed is derived. -/
  seed : Option Nat := none
  /-- Writes a JUnit XML report to this path. -/
  junitPath : Option String := none
  /-- Writes a JSON report to this path. -/
  jsonPath : Option String := none
  /-- Writes a Markdown report to this path. -/
  markdownPath : Option String := none
  /-- Writes the run's events to this path as JSON lines. -/
  eventsPath : Option String := none
  /-- Fails the run if warnings are logged. -/
  wfail : Bool := false
  /--
  How many slots the run's pool has, so how many tests that each take one may run at once. It takes
  precedence over the profile's value; with neither, the pool has as many slots as the runner has
  CPUs available.
  -/
  jobs? : Option Nat := none
  /--
  How long a test may run before it is terminated, in milliseconds. It takes precedence over the
  configuration's value.
  -/
  timeoutMs? : Option Nat := none
  /--
  How long a fixture's setup, prepare, or teardown may run before it is terminated, in milliseconds.
  It takes precedence over the profile's {lit}`fixture-timeout`.
  -/
  fixtureTimeoutMs? : Option Nat := none
  /--
  How long a terminated test has before it is killed, in milliseconds. It takes precedence over the
  configuration's value.
  -/
  gracePeriodMs? : Option Nat := none
  /-- Values of settings, in order, from {lit}`--set NAME=VALUE`. -/
  sets : Array (String × String) := #[]
  /-- The profile of the configuration to run with. -/
  profile : String := "default"
  /-- The filter expressions from {lit}`-E` and {lit}`--filter`, joined by union. -/
  filters : Array String := #[]
  /-- The name filters, from the positional arguments, joined by union. -/
  nameFilters : Array String := #[]
  /-- Whether name filters and {lit}`--skip` patterns match whole names. -/
  exact : Bool := false
  /-- The patterns of {lit}`--skip`: tests whose names contain one are left out. -/
  skips : Array String := #[]
  /-- Whether the tests are drawn from the whole inventory, the default filter set aside. -/
  ignoreDefaultFilter : Bool := false
  /-- What a run that selects no test ends with. -/
  noTests : NoTests := .fail
  /-- When the human-readable output is colored. -/
  color : ColorChoice := .auto
  /-- Whether a run leaves out the progress display that it keeps on a terminal. -/
  hideProgressBar : Bool := false
  /-- The format of what {lit}`list` prints. -/
  messageFormat : MessageFormat := .human
  /--
  The modules from {lit}`--interpreted`, as the command line writes them, whose tests run through
  the interpreted product. The driver acts on them.
  -/
  interpreted : Array String := #[]
  /-- Whether the usage text was asked for. -/
  help : Bool := false
deriving Repr, Inhabited

/--
Whether the command resolves what each test receives, which needs the targets that the profile's
settings name: a run does, and so does a listing that shows the settings.
-/
def Options.resolvesSettings (opts : Options) : Bool :=
  opts.command == .run || opts.verbosity != .silent ||
    opts.messageFormat == .json || opts.messageFormat == .jsonPretty

/-- The form of a duration, as the messages about malformed durations state it. -/
def durationForm : String :=
  "one or more whole numbers, each followed by one of the units h, m, s, ms, used at most once \
  each and in that order, such as 90s, 10m, or 2m30s"

/-- The units of a duration, in the order they are written, each with its length in milliseconds. -/
def durationUnits : List (String × Nat) :=
  [("h", 3600000), ("m", 60000), ("s", 1000), ("ms", 1)]

/--
Parses a duration: a sequence of components such as {lit}`2m30s`, each a whole number followed by a
unit, with the units {lit}`h`, {lit}`m`, {lit}`s`, and {lit}`ms` in that order and each at most
once. Whitespace around it is ignored. The result is in milliseconds.
-/
def parseDuration (s : String) : Except String Nat := Id.run do
  let s := s.trimAscii.copy
  let err := .error s!"invalid duration '{s}': expected {durationForm}"
  let mut cs := s.toList
  if cs.isEmpty then return err
  let mut units := durationUnits
  let mut total := 0
  for _ in durationUnits do
    if cs.isEmpty then break
    let digits := cs.takeWhile Char.isDigit
    let rest := cs.dropWhile Char.isDigit
    let unit := String.ofList (rest.takeWhile Char.isAlpha)
    match units.dropWhile (·.1 != unit) with
    | (_, scale) :: later =>
      if digits.isEmpty then return err
      total := total + (String.ofList digits).toNat! * scale
      units := later
      cs := rest.dropWhile Char.isAlpha
    | [] => return err
  if cs.isEmpty then .ok total else err

/--
Splits a {lit}`--set` value at its first {lit}`=`. The value is everything after it, taken verbatim.
-/
def parseSet (s : String) : Except String (String × String) :=
  match s.splitOn "=" with
  | name :: value@(_ :: _) =>
    if name.isEmpty then .error s!"--set {s}: the setting's name is empty"
    else .ok (name, "=".intercalate value)
  | _ => .error s!"--set {s}: expected NAME=VALUE"

/-- An option of the command line, as the parser and the usage text know it. -/
structure OptionSpec where
  /-- The option's long name, without its dashes, which also identifies it. -/
  long : String
  /-- Its short form with its dash, such as {lit}`-E`, if it has one. -/
  short? : Option String := none
  /-- Other long names for the option, without their dashes. -/
  aliases : List String := []
  /-- The name of its value in messages and the usage text, when it takes a value. -/
  value? : Option String := none
  /-- Whether it may be given more than once. -/
  repeatable : Bool := false
  /-- The commands that it belongs to. -/
  commands : List Command := [.run, .list]
  /-- The heading that the usage text lists it under. -/
  group : String
  /-- What it does, for the usage text. -/
  help : String
deriving Repr, Inhabited

/-- The options of the command line, in the order the usage text lists them. -/
def optionSpecs : Array OptionSpec := #[
  { long := "filter", short? := "-E", value? := "EXPR", repeatable := true, group := "Selection"
    help := "Select the tests that the filter expression selects. Repeatable; several are joined \
      by union." },
  { long := "skip", value? := "PATTERN", repeatable := true, group := "Selection"
    help := "Leave out the tests whose names contain PATTERN. Repeatable." },
  { long := "exact", group := "Selection"
    help := "Match name filters and --skip patterns against whole names." },
  { long := "ignore-default-filter", group := "Selection"
    help := "Draw the tests from the whole inventory, the profile's default filter set aside." },
  { long := "interpreted", value? := "MODULES", repeatable := true, group := "Selection"
    help := "Build the named modules, separated by commas, and run their tests through \
      errata-interpret, which imports them with no link. The libraries that hold them are the \
      test executables. Repeatable." },
  { long := "profile", short? := "-P", value? := "NAME", group := "Configuration"
    help := "The profile of errata.toml to use (ERRATA_PROFILE, or default)." },
  { long := "set", value? := "NAME=VALUE", repeatable := true, group := "Configuration"
    help := "Give a setting a value. Repeatable." },
  { long := "seed", value? := "N", group := "Configuration"
    help := "The run's seed, from which each test's seed is derived." },
  { long := "timeout", value? := "DURATION", group := "Configuration"
    help := "How long a test, or the listing of a test executable, may run before it is \
      stopped, such as 90s or 2m30s (10m)." },
  { long := "fixture-timeout", value? := "DURATION", group := "Configuration"
    help := "How long a fixture's setup, prepare, or teardown may run before it is stopped \
      (the profile's fixture-timeout, or 10m)." },
  { long := "grace-period", value? := "DURATION", group := "Configuration"
    help := "How long a stopped test has before it is killed (10s)." },
  { long := "test-threads", short? := "-j", aliases := ["jobs"], value? := "N", commands := [.run]
    group := "Running", help := "How many tests may run at once (the CPUs available)." },
  { long := "no-tests", value? := "ACTION", commands := [.run], group := "Running"
    help := "What a run that selects no test does: fail, warn (which fails under --wfail), or \
      pass (fail)." },
  { long := "update-golden", commands := [.run], group := "Running"
    help := "Rewrite the expected files of golden checks." },
  { long := "wfail", commands := [.run], group := "Running"
    help := "Fail the run if warnings are logged, so that --no-tests warn exits as fail does." },
  { long := "verbose", short? := "-v", group := "Reporting"
    help := "Also report passes, truncating each test's results; with list, show the settings \
      and what each test receives." },
  { long := "verbose-all", short? := "-vv", group := "Reporting"
    help := "Report every result, without truncation." },
  { long := "verbose-docs", short? := "-vvv", group := "Reporting"
    help := "Report every result and every test's docstring." },
  { long := "color", value? := "WHEN", group := "Reporting"
    help := "Color the output: auto, always, or never (auto: on a terminal, unless NO_COLOR is \
      set; CLICOLOR_FORCE forces it)." },
  { long := "hide-progress-bar", commands := [.run], group := "Reporting"
    help := "Leave out the progress display on a terminal." },
  { long := "message-format", short? := "-T", value? := "FORMAT", commands := [.list]
    group := "Reporting", help := "The format of the list: human, oneline, json, or json-pretty \
      (human)." },
  { long := "junit", value? := "PATH", commands := [.run], group := "Reporting"
    help := "Write a JUnit XML report to PATH, in place of the profile's junit." },
  { long := "json", value? := "PATH", commands := [.run], group := "Reporting"
    help := "Write a JSON report to PATH, in place of the profile's json." },
  { long := "markdown", value? := "PATH", commands := [.run], group := "Reporting"
    help := "Write a Markdown report (for a CI job summary) to PATH, in place of the profile's \
      markdown." },
  { long := "events", value? := "PATH", commands := [.run], group := "Reporting"
    help := "Append the run's events to PATH as JSON lines." },
  { long := "help", short? := "-h", group := "Reporting", help := "Print this text." }
]

/--
Retired options of the command line, by long name, each with the text that the message rejecting it
adds: what does the option's work.
-/
def replacedOptions : List (String × String) := [
  ("test-options", "the arguments after `lake test --` go to the runner as they are: `run` or \
    `list`, then options and filters, such as `-E 'exe(Lib)'` for a library"),
  ("list", "the `list` command lists the tests, and `list -v` shows what each receives")]

/-- One option as the command line gives it: its spec, how it was written, and its value. -/
structure GivenOption where
  /-- The option. -/
  spec : OptionSpec
  /-- How the command line wrote its name. -/
  written : String
  /-- Its value, when it takes one. -/
  value? : Option String := none
deriving Repr, Inhabited

/-- The option with the given long name or alias, without dashes. -/
def findLongOption? (name : String) : Option OptionSpec :=
  optionSpecs.find? fun s => s.long == name || s.aliases.contains name

/--
The option that an argument beginning with a single {lit}`-` names, with the value attached to it:
an exact short form such as {lit}`-vv`, or a short form of an option that takes a value followed
by the value, such as {lit}`-Etag(slow)` or {lit}`-j=1`.
-/
def findShortOption? (arg : String) : Option (OptionSpec × Option String) :=
  match optionSpecs.find? (·.short? == some arg) with
  | some spec => some (spec, none)
  | none => do
    let spec ← optionSpecs.find? fun s =>
      s.value?.isSome && s.short?.any (fun sh => arg.startsWith sh)
    let rest := (arg.drop (spec.short?.getD "").length).copy
    return (spec, some ((rest.dropPrefix? "=").map (·.copy) |>.getD rest))

/--
The options among the arguments, in order, and the positional arguments. An option's value follows
it as the next argument, or is attached with {lit}`=` to a long name or directly to a short one.
Every argument after {lit}`--` is positional.
-/
def splitArguments (args : List String) : Except String (Array GivenOption × Array String) :=
  collectArguments #[] #[] args
where
  /--
  The option that an argument names, and whether its value is the next argument, {name}`next?`.
  The value is {name}`attached?` when the argument has one.
  -/
  withValue (spec : OptionSpec) (written : String) (attached? next? : Option String) :
      Except String (GivenOption × Bool) :=
    match spec.value?, attached?, next? with
    | none, some _, _ => .error s!"{written} takes no value"
    | none, none, _ => .ok ({ spec, written }, false)
    | some _, some v, _ => .ok ({ spec, written, value? := some v }, false)
    | some what, none, some v =>
      -- A next argument that names an option is that option, and the value is missing.
      if namesOption v then .error s!"{written} expects {what}, and {v} is an option"
      else .ok ({ spec, written, value? := some v }, true)
    | some what, none, none => .error s!"{written} expects {what}"
  /-- Whether an argument names an option of the table. -/
  namesOption (arg : String) : Bool :=
    if arg.startsWith "--" then
      (findLongOption? ((arg.drop 2).copy.splitOn "=").head!).isSome
    else arg.startsWith "-" && (findShortOption? arg).isSome
  /--
  The option that an argument beginning with {lit}`-` names, with its value, and whether the value
  is the next argument.
  -/
  optionOf (arg : String) (next? : Option String) : Except String (GivenOption × Bool) :=
    if arg.startsWith "--" then
      let body := (arg.drop 2).copy
      let (name, attached?) := match body.splitOn "=" with
        | n :: v :: vs => (n, some ("=".intercalate (v :: vs)))
        | _ => (body, none)
      match findLongOption? name with
      | none =>
        match replacedOptions.lookup name with
        | some how => .error s!"unknown option '--{name}': {how}"
        | none => .error s!"unknown option '--{name}'"
      | some spec => withValue spec s!"--{name}" attached? next?
    else
      match findShortOption? arg with
      | none => .error s!"unknown option '{arg}'"
      | some (spec, attached?) => withValue spec (spec.short?.getD arg) attached? next?
  /-- Adds the options and positional arguments of the list to those collected so far. -/
  collectArguments (given : Array GivenOption) (positional : Array String) (args : List String) :
      Except String (Array GivenOption × Array String) :=
    match args with
    | [] => .ok (given, positional)
    | "--" :: rest => .ok (given, positional ++ rest.toArray)
    | arg :: rest =>
      if arg.startsWith "-" && arg.length > 1 then
        match optionOf arg rest.head? with
        | .error e => .error e
        | .ok (g, true) => collectArguments (given.push g) positional rest.tail
        | .ok (g, false) => collectArguments (given.push g) positional rest
      else collectArguments given (positional.push arg) rest
  termination_by args.length
  decreasing_by all_goals (simp; try omega)

/-- The rank of a verbosity, so that the most verbose of several options wins. -/
private def verbosityRank : Verbosity → Nat
  | .silent => 0
  | .quiet => 1
  | .verbose => 2
  | .superVerbose => 3

/-- Applies one option to the options read so far. -/
def applyOption (opts : Options) (g : GivenOption) : Except String Options := do
  let value := g.value?.getD ""
  let path : Except String String :=
    if value.isEmpty then .error s!"{g.written} expects a path" else .ok value
  let raise (v : Verbosity) : Options :=
    if verbosityRank v > verbosityRank opts.verbosity then { opts with verbosity := v } else opts
  match g.spec.long with
  | "filter" => return { opts with filters := opts.filters.push value }
  | "skip" => return { opts with skips := opts.skips.push value }
  | "exact" => return { opts with exact := true }
  | "ignore-default-filter" => return { opts with ignoreDefaultFilter := true }
  | "interpreted" =>
    let modules := value.splitOn "," |>.filter (!·.isEmpty)
    if modules.isEmpty then throw s!"{g.written} expects the names of modules"
    return { opts with interpreted := opts.interpreted ++ modules.toArray }
  | "profile" =>
    if value.isEmpty then throw s!"{g.written} expects the name of a profile"
    return { opts with profile := value }
  | "set" => return { opts with sets := opts.sets.push (← parseSet value) }
  | "seed" =>
    let some n := value.toNat? | throw s!"{g.written} expects a whole number, and it is '{value}'"
    return { opts with seed := some n }
  | "timeout" =>
    let ms ← parseDuration value
    if ms == 0 then throw s!"{g.written} must be longer than zero"
    return { opts with timeoutMs? := some ms }
  | "fixture-timeout" =>
    let ms ← parseDuration value
    if ms == 0 then throw s!"{g.written} must be longer than zero"
    return { opts with fixtureTimeoutMs? := some ms }
  | "grace-period" => return { opts with gracePeriodMs? := some (← parseDuration value) }
  | "test-threads" =>
    let some n := value.toNat? | throw s!"{g.written} expects a whole number, and it is '{value}'"
    if n == 0 then throw s!"{g.written} 0 is invalid: at least one test must be able to run"
    return { opts with jobs? := some n }
  | "no-tests" =>
    match value with
    | "fail" => return { opts with noTests := .fail }
    | "warn" => return { opts with noTests := .warn }
    | "pass" => return { opts with noTests := .pass }
    | _ => throw s!"{g.written} expects fail, warn, or pass, and it is '{value}'"
  | "update-golden" => return { opts with updateGolden := true }
  | "wfail" => return { opts with wfail := true }
  | "verbose" => return raise .quiet
  | "verbose-all" => return raise .verbose
  | "verbose-docs" => return raise .superVerbose
  | "color" =>
    match value with
    | "auto" => return { opts with color := .auto }
    | "always" => return { opts with color := .always }
    | "never" => return { opts with color := .never }
    | _ => throw s!"{g.written} expects auto, always, or never, and it is '{value}'"
  | "hide-progress-bar" => return { opts with hideProgressBar := true }
  | "message-format" =>
    match value with
    | "human" => return { opts with messageFormat := .human }
    | "oneline" => return { opts with messageFormat := .oneline }
    | "json" => return { opts with messageFormat := .json }
    | "json-pretty" => return { opts with messageFormat := .jsonPretty }
    | _ => throw s!"{g.written} expects human, oneline, json, or json-pretty, and it is '{value}'"
  | "junit" => return { opts with junitPath := some (← path) }
  | "json" => return { opts with jsonPath := some (← path) }
  | "markdown" => return { opts with markdownPath := some (← path) }
  | "events" => return { opts with eventsPath := some (← path) }
  | "help" => return { opts with help := true }
  | other => throw s!"the option --{other} has no meaning"

/--
Reads the command line that follows the configuration files: {lit}`run` or {lit}`list` when the
first argument is one of those words, and {lit}`run` otherwise; then the options and the name
filters. Options of the other command are errors, and so are options that are not repeatable and
are given twice. The profile is {name}`profileEnv` when the command line names none
and it is not empty.
-/
def parseCommandLine (args : List String) (profileEnv : Option String := none) :
    Except String Options := do
  let (command, args) := match args with
    | "run" :: rest => (Command.run, rest)
    | "list" :: rest => (Command.list, rest)
    | _ => (Command.run, args)
  let (given, positional) ← splitArguments args
  let mut opts : Options := { command, nameFilters := positional }
  if let some p := profileEnv then
    unless p.isEmpty do opts := { opts with profile := p }
  let mut seen : Array String := #[]
  for g in given do
    unless g.spec.commands.contains command do
      let owner := if command == .run then "list" else "run"
      throw s!"{g.written} is an option of `{owner}`, and the command is `{command.name}`"
    if !g.spec.repeatable && seen.contains g.spec.long then
      throw s!"{g.written} is given more than once"
    seen := seen.push g.spec.long
    opts ← applyOption opts g
  return opts

/--
Reads the runner's whole command line: the configuration file that {lit}`errata-config` writes, the
workspace's configuration file that the driver writes, and then what {name}`parseCommandLine` reads.
-/
def parseOptions (args : List String) (profileEnv : Option String := none) :
    Except String Options :=
  match args with
  | config :: workspace :: rest => do
    let opts ← parseCommandLine rest profileEnv
    return { opts with configPath := config, workspacePath := workspace }
  | _ => .error "expected the configuration file and the workspace's configuration file"

/-- How the usage text writes an option: its names, then its value. -/
def OptionSpec.forms (s : OptionSpec) : String :=
  let names := s.short?.toList ++ (s.long :: s.aliases).map ("--" ++ ·)
  ", ".intercalate names ++ (s.value?.map (" " ++ ·)).getD ""

/-- The usage text, with {name}`invocation` as the command that the arguments follow. -/
def usage (invocation : String) : String := Id.run do
  let width := optionSpecs.foldl (fun w s => max w s.forms.length) 0
  let mut out := s!"Runs or lists the tests of the package's test executables.\n\n\
    Usage:\n  {invocation} [run|list] [OPTIONS] [NAME-FILTER]... [-- NAME-FILTER...]\n\n\
    Commands:\n  \
    run   Run the selected tests; the command when the first argument is neither word.\n  \
    list  List the selected tests.\n\n\
    The command is the first argument; after an option, run and list are name filters.\n\n\
    Tests are selected when their names contain a name filter (equal one, under --exact), a\n\
    filter expression selects them, no --skip pattern is in their names, and the profile's\n\
    default filter selects them. Without name filters, or without filter expressions, that\n\
    condition holds for every test. In a filter expression, default() stands for the default\n\
    filter.\n\n\
    A run's summary counts the results by outcome and the listed tests left out, then the test\n\
    libraries and executables that the filters ruled out before building. Ruled-out libraries\n\
    count only when a module of theirs that an earlier build left on disk records a test.\n"
  let mut group := ""
  for s in optionSpecs do
    if s.group != group then
      group := s.group
      out := out ++ s!"\n{group}:\n"
    let only := match s.commands with
      | [.run] => " Run only."
      | [.list] => " List only."
      | _ => ""
    let lead := "".pushn ' ' (width + 4)
    let lines := wrapWords (100 - lead.length) ((s.help ++ only).splitOn " ")
    out := out ++ s!"  {s.forms.pushn ' ' (width + 2 - s.forms.length)}\
      {("\n" ++ lead).intercalate lines}\n"
  out := out ++ "\nThe PATHs of --junit, --json, --markdown, and --events are relative to the \
    directory that\nlake test runs in, and the profile's report paths to the package's directory.\n"
  return out
where
  /-- Words joined into lines of at most {name}`width` characters, a longer word on its own line. -/
  wrapWords (width : Nat) (words : List String) : List String :=
    let (done, current) := words.foldl (init := (#[], "")) fun (done, current) w =>
      if current.isEmpty then (done, w)
      else if current.length + 1 + w.length ≤ width then (done, current ++ " " ++ w)
      else (done.push current, w)
    (done.push current).toList

end Errata.Runner
