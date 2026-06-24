/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.IsTest
public import Errata.Runner
public import Lean
public meta import Lean

open Lean Meta Elab Term

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/--
Verifies that a tagged declaration can be run as a test: it is not {lit}`meta`, and it has an
{name}`IsTest` instance.
-/
meta def checkIsTest (decl : Name) : MetaM Unit := do
  let env ← getEnv
  if isMarkedMeta env decl then
    throwError m!"A test must not be `meta`"
  let info ← getConstInfo decl
  let goal := mkApp (mkConst ``IsTest) info.type
  match ← trySynthInstance goal with
  | .some _ => pure ()
  | _ =>
    throwError m!"`@[test]` requires an `Errata.IsTest` instance for the test's type{indentExpr info.type}"

/--
A recorded test: its declaration name and the source file that defines it. The file is captured
when the attribute is applied; the declaration's line and column are recovered later, once the
declaration ranges are available.
-/
structure TestDecl where
  /-- The test declaration's name. -/
  name : Name
  /-- The source file that defines the test. -/
  file : String
  deriving Inhabited

/--
The tests recorded by {lit}`@[test]`, per module. The attribute is an elaboration-time feature:
tests are recorded as modules are elaborated, and {lit}`getAllTests%` reads them back at elaboration
time to build the runnable test array.
-/
meta initialize testExt : SimplePersistentEnvExtension TestDecl (Array TestDecl) ←
  registerSimplePersistentEnvExtension {
    name := `Errata.test
    addEntryFn := Array.push
    addImportedFn := fun es => es.foldl Array.append #[]
  }

/-- Records a declaration as a test, capturing the source file that defines it. -/
meta def recordTest (decl : Name) : AttrM Unit := do
  (checkIsTest decl).run'
  modifyEnv (testExt.addEntry · { name := decl, file := ← getFileName })

/-- Marks a definition as a test, discovered and run by the Errata test runner. -/
meta initialize
  registerBuiltinAttribute {
    ref := `Errata.test
    name := `test
    descr := "Marks a definition as a test, discovered and run by the Errata test runner."
    applicationTime := .afterTypeChecking
    add := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `test kind
      recordTest decl
  }

/-- The test's name below its module: the declaration's components past the module prefix, dotted. -/
meta def testNameBelow (moduleName declName : Name) : String :=
  let below :=
    if moduleName.isPrefixOf declName then declName.components.drop moduleName.components.length
    else declName.components
  ".".intercalate (below.map (·.toString))

/--
{lit}`getAllTests% "package" Mod.A Mod.B ...` reads the tests recorded by {lit}`@[test]` in the
named modules and expands to the array of {name}`TestEntry` values that run them. Each module must
be imported, with {lit}`import all` for module-system modules, so its tests are reachable.
-/
syntax (name := getAllTests) "getAllTests%" str ident* : term

/-- Expands {lit}`getAllTests%` by reading the recorded tests of the named modules. -/
@[term_elab getAllTests]
meta def elabGetAllTests : TermElab := fun stx expectedType? => do
  let `(getAllTests% $pkg:str $mods:ident*) := stx
    | throwUnsupportedSyntax
  let package := pkg.getString
  let env ← getEnv
  let mut entries : Array Term := #[]
  for modStx in mods do
    let moduleName := modStx.getId
    let some idx := env.getModuleIdx? moduleName | continue
    let moduleStr := moduleName.toString
    for test in testExt.getModuleEntries env idx do
      let userName := privateToUserName test.name
      let testName := testNameBelow moduleName userName
      let range ← findDeclarationRanges? test.name
      let pos := (range.map (·.range.pos)).getD ⟨0, 0⟩
      let endPos := (range.map (·.range.endPos)).getD ⟨0, 0⟩
      entries := entries.push <| ←
        `(Errata.TestEntry.of $(quote package) $(quote moduleStr) $(quote testName)
            (Errata.Location.mk $(quote test.file)
              (Errata.Position.mk $(quote pos.line) $(quote pos.column))
              (Errata.Position.mk $(quote endPos.line) $(quote endPos.column)))
            (@$(mkIdent userName)))
  elabTerm (← `(#[$entries,*])) expectedType?
