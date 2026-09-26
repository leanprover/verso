/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The inventory that the List phase gathers, and what the runner works out from it before the Run
phase: which tests the filters select, what each test receives for the settings it takes, and the
limits it runs under.
-/
module

public import Errata.RunnerConfig
public import Errata.Filter
public import Errata.Protocol

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata.Runner

/-- A setting that a test executable declares. -/
structure SettingInfo where
  /-- The setting's name. -/
  name : String
  /-- The setting's description. -/
  description? : Option String := none
  /-- The value that a test receives when nothing else gives one. -/
  default? : Option String := none
deriving Repr, Inhabited, DecidableEq

/-- A test in the inventory. -/
structure InventoryTest where
  /-- The position of the test's executable in the configuration. -/
  exeIdx : Nat
  /-- The test's name. -/
  name : String
  /-- The components of the test's name. -/
  path : Array String := #[]
  /-- The file that defines the test. -/
  file? : Option String := none
  /-- The line of its declaration. -/
  line? : Option Nat := none
  /-- The test's description. -/
  description? : Option String := none
  /-- The test's tags. -/
  tags : Array String := #[]
  /-- The settings that the test takes, in the order it takes them. -/
  settings : Array String := #[]
  /-- The fixtures that the test uses, each exclusive or shared. -/
  fixtures : Array Protocol.FixtureDep := #[]
  /-- The number of hardware threads that the test asks for, when it asks. -/
  threads? : Option Nat := none
deriving Repr, Inhabited

/-- A fixture in the inventory. -/
structure InventoryFixture where
  /-- The fixture's name. -/
  name : String
  /-- The fixture's description. -/
  description? : Option String := none
  /-- The settings that the fixture takes, in the order it takes them. -/
  settings : Array String := #[]
  /-- The names of the fixtures that the fixture takes, each declared before it. -/
  fixtures : Array String := #[]
  /-- The number of hardware threads that the fixture's phases ask for, when it asks. -/
  threads? : Option Nat := none
deriving Repr, Inhabited

/-- What the List phase gathered from one test executable. -/
structure Listing where
  /-- The settings that the executable declares. -/
  settings : Array SettingInfo := #[]
  /-- The fixtures that the executable declares, each after the fixtures it takes. -/
  fixtures : Array InventoryFixture := #[]
  /-- The executable's tests. -/
  tests : Array InventoryTest := #[]
deriving Repr, Inhabited

/-- The test as a filter sees it. -/
def InventoryTest.record (t : InventoryTest) (exe : String) : Filter.Record where
  name := t.name
  file := t.file?.getD ""
  exe := exe
  tags := t.tags

/-- How long a test may run when nothing sets it: ten minutes. -/
def defaultTimeoutMs : Nat := 10 * 60 * 1000

/-- How long a terminated test has before it is killed when nothing sets it: ten seconds. -/
def defaultGracePeriodMs : Nat := 10 * 1000

/-- How long a test runs before the report marks it slow when nothing sets it: a minute. -/
def defaultSlowAfterMs : Nat := 60 * 1000

/-- A filter parsed from its text, with the text and where it came from. -/
structure SourcedFilter where
  /-- The parsed filter. -/
  expr : Filter.Expr
  /-- The filter's text. -/
  text : String
  /-- Where its text came from. -/
  source : Filter.Source
deriving Repr, Inhabited

/-- Parses a filter's text, with an error that names its place. -/
def SourcedFilter.parse (text : String) (source : Filter.Source) : Except String SourcedFilter :=
  match Filter.parse text with
  | .ok expr => .ok { expr, text, source }
  | .error e => .error (e.render source)

/-- The place {name}`offset` characters into the filter's text, as a message's prefix. -/
def SourcedFilter.at (f : SourcedFilter) (offset : Nat) : String :=
  f.source.at offset

/--
The tests that a run selects: those that one of the filter expressions selects, whose names contain
one of the name filters and no skip pattern, and that the default filter selects unless it is set
aside. Without filter expressions, or without name filters, that part holds for every test.
-/
structure Selection where
  /-- The command line's filter expressions, joined by union. -/
  filters : Array SourcedFilter := #[]
  /-- The command line's name filters, joined by union. -/
  names : Array String := #[]
  /-- The patterns of {lit}`--skip`. -/
  skips : Array String := #[]
  /-- Whether name filters and skip patterns match whole names. -/
  exact : Bool := false
  /-- The profile's default filter, which {lit}`default()` stands for in the filter expressions. -/
  default? : Option SourcedFilter := none
  /-- Whether the tests are drawn from the default filter. -/
  useDefault : Bool := true
deriving Inhabited

/-- Whether a name filter or a skip pattern matches a test's name. -/
def Selection.nameMatches (s : Selection) (pattern name : String) : Bool :=
  if s.exact then name == pattern else (name.find? pattern).isSome

/-- Whether the default filter selects a test. If there is no default filter, then it is true. -/
def Selection.defaultSelects (s : Selection) (r : Filter.Record) : Bool :=
  (s.default?.map (·.expr.eval r)).getD true

/-- Whether the run selects a test. -/
def Selection.selects (s : Selection) (r : Filter.Record) : Bool :=
  let d := s.defaultSelects r
  (s.filters.isEmpty || s.filters.any (·.expr.eval r d)) &&
    (s.names.isEmpty || s.names.any (s.nameMatches · r.name)) &&
    !s.skips.any (s.nameMatches · r.name) && (!s.useDefault || d)

/--
Whether the run can select a test of the executable named {name}`exe`, judged from the executable's
name alone. The answer is false only when the filter expressions or the default filter select no
test of any executable with that name, whatever its tests are.
-/
def Selection.mayContain (s : Selection) (exe : String) : Bool :=
  let d := (s.default?.map (·.expr.evalExe exe)).getD (some true)
  let noFilterSelects := !s.filters.isEmpty && s.filters.all (·.expr.evalExe exe d == some false)
  !(noFilterSelects || (s.useDefault && d == some false))

/-- What the runner resolves a test's configuration from, besides the test itself. -/
structure ResolutionContext where
  /-- Values of settings from the command line, in order; the last one for a name counts. -/
  sets : Array (String × String) := #[]
  /-- The selected profile. -/
  profile : Profile := { name := "default" }
  /-- The profile's overrides, each with its parsed filter. -/
  overrides : Array (SourcedFilter × Override) := #[]
  /-- The default filter, which {lit}`default()` stands for in the overrides' filters. -/
  default? : Option SourcedFilter := none
  /-- The command line's timeout, in milliseconds. -/
  timeoutMs? : Option Nat := none
  /-- The command line's grace period, in milliseconds. -/
  gracePeriodMs? : Option Nat := none
  /-- Whether the command line asks golden checks to rewrite their expected files. -/
  updateGolden : Bool := false
  /-- The run's seed. -/
  runSeed : Nat := 0

/--
The seed that a test receives: the run's seed mixed with the executable's and the test's names, so
that each test draws from its own stream and adding a test changes no other test's seed.
-/
def testSeed (runSeed : Nat) (exe test : String) : Nat :=
  (mixHash (mixHash (hash runSeed) (hash exe)) (hash test)).toNat

/-- The name of Errata's seed setting, whose value the runner derives for each test. -/
def seedSetting : String := "Errata.seed"

/--
The name of Errata's setting that the Lean harness reads to rewrite golden files, which the runner
gives the value {lit}`true` under {lit}`--update-golden`.
-/
def updateGoldenSetting : String := "Errata.updateGolden"

/-- What a test runs with, as the runner resolved it. -/
structure Resolved where
  /-- The values of the settings it takes that have one, in the order it takes them. -/
  settings : Array (String × String) := #[]
  /-- The mandatory settings that nothing gives a value. -/
  missing : Array String := #[]
  /-- How long it may run, in milliseconds. -/
  timeoutMs : Nat := defaultTimeoutMs
  /-- How long it has after it is terminated, in milliseconds. -/
  gracePeriodMs : Nat := defaultGracePeriodMs
  /-- How long it runs before the report marks it slow, in milliseconds. -/
  slowAfterMs : Nat := defaultSlowAfterMs
  /-- Whether its golden checks rewrite their expected files. -/
  updateGolden : Bool := false
  /-- Whether its seed is the one derived from the run's seed. -/
  derivedSeed : Bool := false
deriving Repr, Inhabited, DecidableEq

/--
The values of the settings {name}`deps` that the test or fixture {name}`name` of the executable
{name}`exe` takes, with the mandatory ones that nothing gives a value, and whether the seed is the
derived one. Each value comes from the command line, then the first of {name}`overrides` that gives
it, then the profile, then the setting's declared default, and, for {lit}`Errata.seed`, the seed
derived from the run's seed and {name}`name`.
-/
def ResolutionContext.resolveSettings (ctx : ResolutionContext) (exe : String)
    (declared : Array SettingInfo) (name : String) (deps : Array String)
    (overrides : Array Override) : Array (String × String) × Array String × Bool := Id.run do
  let mut settings := #[]
  let mut missing := #[]
  let mut derivedSeed := false
  for dep in deps do
    let given? :=
      ((ctx.sets.findRev? (·.1 == dep)).map (·.2))
      <|> overrides.findSome? (fun o => (o.settings.find? (·.1 == dep)).map (·.2))
      <|> (ctx.profile.settings.find? (·.1 == dep)).map (·.2)
      <|> (declared.find? (·.name == dep)).bind (·.default?)
    match given? with
    | some v => settings := settings.push (dep, v)
    | none =>
      if dep == seedSetting then
        settings := settings.push (dep, toString (testSeed ctx.runSeed exe name))
        derivedSeed := true
      else missing := missing.push dep
  return (settings, missing, derivedSeed)

/--
Resolves what a fixture's phases receive: each setting the fixture takes from the command line,
then the profile, then the setting's declared default, and, for {lit}`Errata.seed`, the seed derived
from the run's seed and the fixture's name. The timeout is the profile's {lit}`fixture-timeout`, and
the grace period comes from the command line, then the profile.
-/
def ResolutionContext.resolveFixture (ctx : ResolutionContext) (exe : String)
    (declared : Array SettingInfo) (f : InventoryFixture) : Resolved :=
  let (settings, missing, derivedSeed) := ctx.resolveSettings exe declared f.name f.settings #[]
  { settings, missing, derivedSeed
    timeoutMs := ctx.profile.fixtureTimeoutMs?.getD defaultTimeoutMs
    gracePeriodMs := ctx.gracePeriodMs? <|> ctx.profile.gracePeriodMs? |>.getD defaultGracePeriodMs
    slowAfterMs := ctx.profile.slowAfterMs?.getD defaultSlowAfterMs }

/--
Resolves what a test receives. Each setting the test takes comes from the command line, then the
first override that matches the test and gives it, then the profile, then the setting's declared
default, and, for {lit}`Errata.seed`, the seed derived from the run's seed. The timeout and the
grace period come from the command line, the first matching override, the profile, and the defaults,
in that order; the slow mark and golden updating come from the first matching override, the
profile, and the defaults, with {lit}`--update-golden` over all of them.
-/
def ResolutionContext.resolve (ctx : ResolutionContext) (exe : String)
    (declared : Array SettingInfo) (t : InventoryTest) : Resolved := Id.run do
  let record := t.record exe
  let dflt := (ctx.default?.map (·.expr.eval record)).getD true
  let matching := ctx.overrides.filterMap fun (f, o) =>
    if f.expr.eval record dflt then some o else none
  let fromOverrides {α} (field : Override → Option α) : Option α := matching.findSome? field
  let (settings, missing, derivedSeed) :=
    ctx.resolveSettings exe declared t.name t.settings matching
  return {
    settings, missing, derivedSeed
    timeoutMs := ctx.timeoutMs? <|> fromOverrides (·.timeoutMs?) <|> ctx.profile.timeoutMs?
      |>.getD defaultTimeoutMs
    gracePeriodMs := ctx.gracePeriodMs? <|> fromOverrides (·.gracePeriodMs?) <|>
      ctx.profile.gracePeriodMs? |>.getD defaultGracePeriodMs
    slowAfterMs := fromOverrides (·.slowAfterMs?) <|> ctx.profile.slowAfterMs?
      |>.getD defaultSlowAfterMs
    updateGolden := ctx.updateGolden ||
      (fromOverrides (·.updateGolden?) <|> ctx.profile.updateGolden? |>.getD false)
  }

/-- A value given to a setting that no test executable declares. -/
structure Undeclared where
  /-- The setting's name. -/
  name : String
  /-- Where the value was given. -/
  place : String
  /-- Whether the command line gave it. -/
  commandLine : Bool
deriving Repr, Inhabited, DecidableEq

/--
The places where the command line, the profile, or its overrides give {lit}`Errata.updateGolden` a
value, each as an error message. The run sets that setting through {lit}`--update-golden` and the
{lit}`update-golden` key alone, so that every test receives the same value.
-/
def ResolutionContext.updateGoldenValues (ctx : ResolutionContext) : Array String := Id.run do
  let message (place : String) : String :=
    s!"{place} gives the setting {updateGoldenSetting} a value; set it with --update-golden or \
      with the update-golden key of a profile or an override"
  let mut out := #[]
  if ctx.sets.any (·.1 == updateGoldenSetting) then out := out.push (message "--set")
  if ctx.profile.settings.any (·.1 == updateGoldenSetting) then
    out := out.push (message s!"the profile {ctx.profile.name}")
  for (f, o) in ctx.overrides do
    if o.settings.any (·.1 == updateGoldenSetting) then
      out := out.push (message s!"the override at {f.at 0}")
  return out

/--
The names that the command line, the profile, and its overrides give values to without any test
executable declaring them, each with where it was given.
-/
def ResolutionContext.undeclared (ctx : ResolutionContext) (declared : Array String) :
    Array Undeclared := Id.run do
  let mut out := #[]
  for (k, _) in ctx.sets do
    unless declared.contains k do out := out.push { name := k, place := "--set", commandLine := true }
  for (k, _) in ctx.profile.settings do
    unless declared.contains k do
      out := out.push { name := k, place := s!"the profile {ctx.profile.name}", commandLine := false }
  for (f, o) in ctx.overrides do
    for (k, _) in o.settings do
      unless declared.contains k do
        out := out.push { name := k, place := s!"the override at {f.at 0}", commandLine := false }
  return out

/--
The warnings about a filter once the inventory is known, each at the place in the filter's text: a
{lit}`tag(…)` that matches no test's tag, an {lit}`exe(…)` that names no test executable, and a
filter that selects no test. Filters made only of {lit}`all()`, {lit}`none()`, and {lit}`default()`
select what they say, so they draw no warning. {name}`dflt` says whether the default filter selects
a test.
-/
def SourcedFilter.warnings (f : SourcedFilter) (records : Array Filter.Record)
    (exes : Array String) (dflt : Filter.Record → Bool := fun _ => true) :
    Array String := Id.run do
  let mut out := #[]
  let atoms := f.expr.atoms
  for (pred, m, span) in atoms do
    let text := s!"{pred.keyword}({m.print pred})"
    match pred with
    | .tag =>
      unless records.any (·.tags.any m.matches) do
        out := out.push s!"{f.at span.start}: {text} matches no tag of any test"
    | .exe =>
      unless exes.any m.matches do
        out := out.push s!"{f.at span.start}: {text} matches no test executable"
    | _ => pure ()
  unless atoms.isEmpty || records.any (fun r => f.expr.eval r (dflt r)) do
    out := out.push s!"{f.at f.expr.span.start}: the filter selects no test"
  return out

end Errata.Runner
