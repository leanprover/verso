/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The record of the tests that `@[test]` marks and the helpers that `@[test_helper]` marks, kept in
environment extensions. Discovery reads them at elaboration time, and the single-test runner reads
the tests from an imported environment at run time.
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

/--
A recorded test: its declaration name, the definition that runs it, and the source file that
defines it. The file is captured when the attribute is applied; the declaration's line and column
are recovered later, once the declaration ranges are available.
-/
structure TestDecl where
  /-- The test declaration's name. -/
  name : Name
  /-- The exported definition beside the test whose value is the action that runs it. -/
  run : Name
  /-- Whether the action is unsafe, as it is when the test is. -/
  isUnsafe : Bool
  /-- The source file that defines the test. -/
  file : String
  /-- The test's docstring, rendered as Markdown, captured when the attribute is applied. -/
  docstring? : Option String := none
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
subprocess of its own test executable. The file and the docstring are captured when the attribute is
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
  The helper's docstring as {lit}`findDocString?` returns it when the attribute is applied: a
  Markdown docstring as written, and a Verso docstring rendered as Markdown.
  -/
  docstring? : Option String := none
deriving Inhabited

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
