/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The interpreted product of the Lean harness: one fixed executable that imports test modules and runs
the harness over the tests and helpers that they record, with no generated main and no link.
-/
module

public import Errata
public meta import Lean

open Lean Meta

/--
The tables that the Lean harness runs over, read from an imported environment: the tests of the
named modules, and the helpers of every imported module.
-/
structure Tables where
  /-- The tests, in the order of the modules and, within a module, in the order recorded. -/
  entries : Array Errata.TestEntry := #[]
  /-- The helpers, which a test starts through the harness's {lit}`errata-helper` mode. -/
  helpers : Array Errata.Helper := #[]

/-- The type {lean}`Array (String × String) → Errata.TestM Unit` of a test's recorded action. -/
def runType : Expr :=
  let pairs := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``String) (mkConst ``String)
  mkForall `settings .default (mkApp (mkConst ``Array [.zero]) pairs)
    (mkApp (mkConst ``Errata.TestM) (mkConst ``Unit))

/-- The type {lean}`List String → IO UInt32` of a helper. -/
def helperType : Expr :=
  mkForall `args .default (mkApp (mkConst ``List [.zero]) (mkConst ``String))
    (mkApp (mkConst ``IO) (mkConst ``UInt32))

/--
The test entry for a recorded test of the module {name}`module`, as {lit}`getAllTests%` builds it:
the action is the recorded definition, evaluated by name, and each setting has its docstring as its
description and its declared default, read from the setting's value.
-/
unsafe def entryOf (module : Name) (test : Errata.TestDecl) : MetaM Errata.TestEntry := do
  let env ← getEnv
  let run ← evalExpr (Array (String × String) → Errata.TestM Unit) runType (mkConst test.run)
    (safety := .unsafe)
  let settings ← test.settings.mapM fun use => do
    let default? ← evalExpr (Option String) (mkApp (mkConst ``Option [.zero]) (mkConst ``String))
      (mkApp (mkConst ``Errata.Setting.default?) (mkConst use.decl)) (safety := .unsafe)
    let description? :=
      (Errata.settingExt.getState env).find? (·.decl == use.decl) |>.bind (·.docstring?)
    return ({ name := Errata.settingNameOf use.decl, optional := use.optional, description?,
              default? } : Errata.SettingRef)
  let userName := privateToUserName test.name
  return {
    package := "", moduleName := module.toString
    name := userName.toString
    path := userName.components.map (·.toString (escape := false)) |>.toArray
    location := ← Errata.testLocation test
    docstring? := test.docstring?, tags := test.tags, settings, run
  }

/--
The tests that the modules in {name}`modules` record, each module read once. Every module must be
imported.
-/
unsafe def testsOf (modules : Array Name) : MetaM (Array Errata.TestEntry) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut out := #[]
  for module in modules do
    if seen.contains module then continue
    seen := seen.insert module
    let some idx := env.getModuleIdx? module
      | throwError "the module {module} is not imported"
    for test in Errata.testExt.getModuleEntries env idx do
      out := out.push (← entryOf module test)
  return out

/-- The helpers that every imported module records, each named by its fully qualified name. -/
unsafe def helpersOf : MetaM (Array Errata.Helper) := do
  let env ← getEnv
  let mut out := #[]
  for idx in [0 : env.allImportedModuleNames.size] do
    for helper in Errata.helperExt.getModuleEntries env idx do
      let run ← evalExpr (List String → IO UInt32) helperType (mkConst helper.name)
        (safety := .unsafe)
      out := out.push { name := helper.name.toString, run }
  return out

/-- The tables of the modules in {name}`modules`, read from the current environment. -/
unsafe def tablesOf (modules : Array Name) : MetaM Tables := do
  return { entries := ← testsOf modules, helpers := ← helpersOf }

/-- The usage message of the interpreted product. -/
def usage : String :=
  "usage: errata-interpret MODULE... -- <mode> [ARG]...\n\n\
    Imports the modules and runs the Lean harness over the tests they record, as a library's \
    compiled test executable does. The arguments after `--` are those of the test executable:\n\n" ++
    Errata.Harness.usage

/--
Splits the arguments at the first {lit}`--` into the modules before it and the harness's arguments
after it, or gives {lean}`none` when there is no {lit}`--` or no module.
-/
def splitArgs (args : List String) : Option (Array Name × List String) :=
  match args.span (· != "--") with
  | (modules@(_ :: _), _ :: rest) => some (modules.toArray.map String.toName, rest)
  | _ => none

/--
Imports the modules, reads the tables, and runs the harness with the arguments after {lit}`--`. The
modules are found through the search path that {lit}`LEAN_PATH` gives.
-/
unsafe def interpret (args : List String) : IO UInt32 := do
  let some (modules, harnessArgs) := splitArgs args
    | IO.eprintln usage
      return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let imports := #[{ module := `Errata : Import }] ++ modules.map ({ module := · })
  let env ← importModules imports {} (loadExts := true)
  let coreCtx : Core.Context := { fileName := "<errata-interpret>", fileMap := default }
  let (tables, _) ← ((tablesOf modules).run' {} {}).toIO coreCtx { env }
  -- A test's helpers run through this same command, with the same modules.
  let invocation := #[(← IO.appPath).toString] ++ args.toArray.extract 0 (modules.size + 1)
  Errata.Harness.main tables.entries harnessArgs tables.helpers invocation

@[implemented_by interpret]
opaque interpretImpl (args : List String) : IO UInt32

/--
The interpreted product of the Lean harness: {lit}`errata-interpret MODULE... -- <mode> [ARG]...`
imports the modules with {lit}`Errata`, reads the tests that the modules record and the helpers that
every imported module records, and runs {name}`Errata.Harness.main` over them with the arguments
after {lit}`--`. Every mode of the harness behaves as it does in a library's compiled test executable;
a test's helpers run through this same command and modules.
-/
public def main (args : List String) : IO UInt32 := do
  try interpretImpl args catch e => do
    IO.eprintln s!"errata-interpret: {e}"
    return 1
