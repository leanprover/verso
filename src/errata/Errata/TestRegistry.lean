/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The record of the tests that `@[test]` marks, the settings that `@[setting]` marks, the fixtures
that `@[fixture]` marks, and the helpers that `@[test_helper]` marks, kept in environment
extensions. Discovery reads them at elaboration time, and the single-test runner reads the tests
from an imported environment at run time.
-/
module

public import Lean.EnvExtension
public import Lean.DeclarationRange
public import Errata.Result

open Lean

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/-- The name of the setting that a declaration declares: its fully qualified name. -/
def settingNameOf (decl : Name) : String :=
  decl.toString (escape := false)

/--
A setting that a test or a fixture takes as a parameter, with the setting's docstring and declared
default as {lit}`@[setting]` recorded them, so that a test executable lists the setting from this
record alone.
-/
structure SettingUse where
  /-- The declaration of the setting, which {lit}`@[setting]` marks. -/
  decl : Name
  /-- Whether the parameter is an {name}`Option`, so that the test runs without a value. -/
  optional : Bool
  /-- The setting's docstring in Markdown. -/
  description? : Option String := none
  /-- The setting's declared default. -/
  default? : Option String := none
deriving Inhabited, Repr, BEq

/-- A fixture that a test takes as a parameter. -/
structure FixtureUse where
  /-- The declaration of the fixture, which {lit}`@[fixture]` marks. -/
  decl : Name
  /-- Whether the test uses the fixture alone among its users, which it does unless it is shared. -/
  exclusive : Bool
deriving Inhabited, Repr, BEq

/--
A recorded fixture: a declaration whose type, after its parameters, is {lit}`Errata.Fixture`, which
{lit}`@[fixture]` marks. The fixture's name is the declaration's fully qualified name.
-/
structure FixtureDecl where
  /-- The fixture's declaration name. -/
  name : Name
  /--
  The exported definition beside the fixture whose value runs one of its phases. It receives the
  settings and the fixtures' values as name and value pairs, the phase, and the fixture's own value
  when the phase receives it, and returns the value that the setup produced.
  -/
  run : Name
  /-- Whether the definition is unsafe, as it is when the fixture is. -/
  isUnsafe : Bool
  /-- The source file that declares the fixture. -/
  file : String
  /-- The fixture's docstring in Markdown, which describes it in the inventory. -/
  docstring? : Option String := none
  /-- The settings that the fixture takes as parameters, in the order of its parameters. -/
  settings : Array SettingUse := #[]
  /-- The fixtures that the fixture takes as parameters, in the order of its parameters. -/
  fixtures : Array Name := #[]
  /-- The number of hardware threads that the fixture's phases ask for, when it asks. -/
  threads? : Option Nat := none
deriving Inhabited

/--
A recorded test: its declaration name, the definition that runs it, the source file that defines
it, and what a test executable lists about it. The file, the docstring, the settings, and the
fixtures are captured when the attribute is applied; the declaration's range is added when the
module is written, once the declaration ranges are available.
-/
structure TestDecl where
  /-- The test declaration's name. -/
  name : Name
  /--
  The exported definition beside the test whose value runs it. It receives the settings and the
  fixtures' values as name and value pairs, parses the ones the test takes, and applies the test to
  them.
  -/
  run : Name
  /-- Whether the action is unsafe, as it is when the test is. -/
  isUnsafe : Bool
  /-- The source file that defines the test. -/
  file : String
  /--
  The test's declaration range in its source file, which the module's {lit}`.olean` file records.
  -/
  location? : Option Location := none
  /-- The test's docstring, rendered as Markdown, captured when the attribute is applied. -/
  docstring? : Option String := none
  /-- The test's tags, from the attribute's {lit}`tags` argument. -/
  tags : Array String := #[]
  /-- The number of hardware threads that the test asks for, from the attribute's {lit}`threads`. -/
  threads? : Option Nat := none
  /-- The settings that the test takes as parameters, in the order of its parameters. -/
  settings : Array SettingUse := #[]
  /-- The fixtures that the test takes as parameters, in the order of its parameters. -/
  fixtures : Array FixtureUse := #[]
  /--
  The fixtures that the test uses, directly or through other fixtures, each after the fixtures it
  takes.
  -/
  reachedFixtures : Array FixtureDecl := #[]
deriving Inhabited

/--
The fixtures recorded by {lit}`@[fixture]`. The state holds the fixtures of every imported module
and of the current one, so a test's parameter is checked against all of them, in an order in which
each fixture follows the fixtures it takes.
-/
initialize fixtureExt : SimplePersistentEnvExtension FixtureDecl (Array FixtureDecl) ←
  registerSimplePersistentEnvExtension {
    name := `Errata.fixture
    addEntryFn := Array.push
    addImportedFn := fun imported => imported.flatten
  }

/--
The fixtures among {name}`known` that the fixtures {name}`names` are or take, directly or through
other fixtures, in the order of {name}`known`, which lists each fixture after the fixtures it takes.
-/
def reachedFixtureDecls (known : Array FixtureDecl) (names : Array Name) : Array FixtureDecl :=
  Id.run do
    let mut needed : NameSet := names.foldl NameSet.insert {}
    -- Each fixture's own fixtures come before it, so one pass from the last fixture to the first
    -- reaches every fixture that a needed one takes.
    for f in known.reverse do
      if needed.contains f.name then needed := f.fixtures.foldl NameSet.insert needed
    return known.filter (needed.contains ·.name)

/--
The test's own source range, which a failure with no more specific place is reported at: the range
that the module's {lit}`.olean` file records, or else the range that the environment holds for the
declaration, in the file recorded when {lit}`@[test]` was applied.
-/
def testLocation [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (test : TestDecl) : m Location := do
  if let some loc := test.location? then return loc
  let range ← findDeclarationRanges? test.name
  return {
    file := test.file
    startPos := (range.map (·.range.pos)).getD ⟨0, 0⟩
    endPos := (range.map (·.range.endPos)).getD ⟨0, 0⟩
  }

/--
The test with its declaration range from the environment, when the environment holds one. The
declaration ranges of a module's own declarations are complete once the module is elaborated, which
is when its {lit}`.olean` file is written.
-/
def TestDecl.withRange (env : Environment) (test : TestDecl) : TestDecl :=
  if test.location?.isSome then test
  else
    let ranges? := declRangeExt.find? (level := .exported) env test.name <|>
      declRangeExt.find? (level := .server) env test.name
    match ranges? with
    | some r =>
      { test with location? := some { file := test.file, startPos := r.range.pos,
                                      endPos := r.range.endPos } }
    | none => test

/--
The tests recorded by {lit}`@[test]`, per module. Tests are recorded as modules are elaborated;
{lit}`getAllTests%` reads them back at elaboration time to build the runnable test array, the
interpreted product reads them from an imported environment to run them, and from the modules'
{lit}`.olean` files to list them. The {lit}`.olean` file records each test with its declaration
range.
-/
initialize testExt : SimplePersistentEnvExtension TestDecl (Array TestDecl) ←
  registerSimplePersistentEnvExtension {
    name := `Errata.test
    addEntryFn := Array.push
    addImportedFn := fun _ => #[]
    exportEntriesFnEx? := some fun env _ entries =>
      .uniform (entries.toArray.map (·.withRange env))
  }

/--
A recorded helper: a declaration of type {lean}`List String → IO UInt32` that a test runs as a
subprocess of its own test executable. The attribute captures the file and the docstring when it is
applied.
-/
structure HelperDecl where
  /-- The helper declaration's fully qualified name. -/
  name : Name
  /-- Whether the helper is unsafe. -/
  isUnsafe : Bool
  /-- The source file that defines the helper. -/
  file : String
  /--
  The helper's docstring in Markdown, if it has one: a Markdown docstring as written, or a Verso
  docstring rendered as Markdown.
  -/
  docstring? : Option String := none
deriving Inhabited

/--
A recorded setting: a declaration of type {lit}`Errata.Setting` that {lit}`@[setting]` marks. The
setting's name, in the configuration and on the command line, is the declaration's fully qualified
name.
-/
structure SettingDecl where
  /-- The setting's declaration name. -/
  decl : Name
  /-- The source file that declares the setting. -/
  file : String
  /-- The setting's docstring in Markdown, which describes it in the inventory. -/
  docstring? : Option String := none
  /-- The setting's declared default, read from its value when {lit}`@[setting]` is applied. -/
  default? : Option String := none
deriving Inhabited

/-- The name of a setting: its fully qualified declaration name. -/
def SettingDecl.settingName (s : SettingDecl) : String :=
  settingNameOf s.decl

/--
The settings recorded by {lit}`@[setting]`. The state holds the settings of every imported module and
of the current one, so a test's parameter is checked against all of them.
-/
initialize settingExt : SimplePersistentEnvExtension SettingDecl (Array SettingDecl) ←
  registerSimplePersistentEnvExtension {
    name := `Errata.setting
    addEntryFn := Array.push
    addImportedFn := fun imported => imported.flatten
  }

/--
The helpers recorded by {lit}`@[test_helper]`, per module. {lit}`getAllHelpers%` reads them back at
elaboration time to build the table of helpers that a test executable runs by name.
-/
initialize helperExt : SimplePersistentEnvExtension HelperDecl (Array HelperDecl) ←
  registerSimplePersistentEnvExtension {
    name := `Errata.testHelper
    addEntryFn := Array.push
    addImportedFn := fun _ => #[]
  }
