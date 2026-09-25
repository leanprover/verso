/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The record of the tests that `@[test]` marks, the settings that `@[setting]` marks, and the helpers
that `@[test_helper]` marks, kept in environment extensions. Discovery reads them at elaboration
time, and the single-test runner reads the tests from an imported environment at run time.
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

/-- A setting that a test takes as a parameter. -/
structure SettingUse where
  /-- The declaration of the setting, which {lit}`@[setting]` marks. -/
  decl : Name
  /-- Whether the parameter is an {name}`Option`, so that the test runs without a value. -/
  optional : Bool
deriving Inhabited, Repr, BEq

/--
A recorded test: its declaration name, the definition that runs it, and the source file that
defines it. The file is captured when the attribute is applied; the declaration's line and column
are recovered later, once the declaration ranges are available.
-/
structure TestDecl where
  /-- The test declaration's name. -/
  name : Name
  /--
  The exported definition beside the test whose value runs it. It receives the settings as
  name and value pairs, parses the ones the test takes, and applies the test to them.
  -/
  run : Name
  /-- Whether the action is unsafe, as it is when the test is. -/
  isUnsafe : Bool
  /-- The source file that defines the test. -/
  file : String
  /-- The test's docstring, rendered as Markdown, captured when the attribute is applied. -/
  docstring? : Option String := none
  /-- The test's tags, from the attribute's {lit}`tags` argument. -/
  tags : Array String := #[]
  /-- The settings that the test takes as parameters, in the order of its parameters. -/
  settings : Array SettingUse := #[]
deriving Inhabited

/--
The test's own source range, which a failure with no more specific place is reported at. The file is
the one recorded when {lit}`@[test]` was applied, and the line and column come from the declaration
ranges, which are available once the declaration has been elaborated.
-/
def testLocation [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (test : TestDecl) : m Location := do
  let range ← findDeclarationRanges? test.name
  return {
    file := test.file
    startPos := (range.map (·.range.pos)).getD ⟨0, 0⟩
    endPos := (range.map (·.range.endPos)).getD ⟨0, 0⟩
  }

/--
The tests recorded by {lit}`@[test]`, per module. Tests are recorded as modules are elaborated;
{lit}`getAllTests%` reads them back at elaboration time to build the runnable test array, and the
single-test runner reads them from an imported environment at run time.
-/
initialize testExt : SimplePersistentEnvExtension TestDecl (Array TestDecl) ←
  registerSimplePersistentEnvExtension {
    name := `Errata.test
    addEntryFn := Array.push
    addImportedFn := fun _ => #[]
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
