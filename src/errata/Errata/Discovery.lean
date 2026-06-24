/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.IsTest
public import Errata.Runner
public import Lean

open Lean Meta

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/--
Verifies that a tagged declaration can be run as a test: it is not {lit}`meta`, and it has an
{name}`IsTest` instance.
-/
def checkIsTest (decl : Name) : MetaM Unit := do
  let env ← getEnv
  if isMarkedMeta env decl then
    throwError m!"A test must not be `meta`"
  let info ← getConstInfo decl
  let goal := mkApp (mkConst ``IsTest) info.type
  match ← trySynthInstance goal with
  | .some _ => pure ()
  | _ =>
    throwError m!"`@[test]` requires an `Errata.IsTest` instance for the test's type{indentExpr info.type}"

/-- The attribute that marks Errata tests, holding the tagged declarations per module. -/
initialize testAttr : TagAttribute ←
  registerTagAttribute `test
    "Marks a definition as a test, discovered and run by the Errata test runner."
    (validate := fun decl => (checkIsTest decl).run')

/-- The internal names of the Errata tests defined directly in a module. -/
def testsInModule (env : Environment) (moduleName : Name) : Array Name :=
  match env.getModuleIdx? moduleName with
  | some idx => testAttr.ext.getModuleEntries env idx
  | none => #[]
