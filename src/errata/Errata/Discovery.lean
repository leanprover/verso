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
Builds the action that runs a declaration as a test, using the {name}`IsTest` instance for its type
that is visible at the declaration. The declaration must not be {lit}`meta` or universe polymorphic.
-/
meta def testAction (decl : Name) : MetaM Expr := do
  let env ← getEnv
  if isMarkedMeta env decl then
    throwError m!"A test must not be `meta`"
  let info ← getConstInfo decl
  unless info.levelParams.isEmpty do
    throwError m!"A test must not be universe polymorphic"
  let goal := mkApp (mkConst ``IsTest) info.type
  match ← trySynthInstance goal with
  | .some inst =>
    return mkApp3 (mkConst ``IsTest.toTest) info.type (← instantiateMVars inst) (mkConst decl)
  | _ =>
    throwError m!"`@[test]` requires an `Errata.IsTest` instance for the test's type{indentExpr info.type}"

/--
A recorded test: its declaration name, the definition that runs it, and the source file that
defines it. The file is captured when the attribute is applied; the declaration's line and column
are recovered later, once the declaration ranges are available.
-/
structure TestDecl where
  /-- The test declaration's name. -/
  name : Name
  /-- The private definition beside the test whose value is the action that runs it. -/
  run : Name
  /-- Whether the action is unsafe, as it is when the test is. -/
  isUnsafe : Bool
  /-- The source file that defines the test. -/
  file : String
  /-- The test's docstring, rendered as Markdown, captured when the attribute is applied. -/
  docstring? : Option String := none
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
    addImportedFn := fun _ => #[]
  }

/--
Records a declaration as a test. The action that runs it is compiled into a private definition
beside it, so the {name}`IsTest` instance in force here is the one that runs it wherever it is run.
The docstring is read here, while it is still in the live environment, since a downstream build does
not load the imported docstrings.
-/
meta def recordTest (decl : Name) : AttrM Unit := do
  let action ← (testAction decl).run'
  let run := mkPrivateName (← getEnv) (← mkFreshUserName (privateToUserName decl ++ `run))
  let type := mkApp (mkConst ``TestM) (mkConst ``Unit)
  let val ← mkDefinitionValInferringUnsafe run [] type action .opaque
  addAndCompile (.defnDecl val)
  let docstring? ← findDocString? (← getEnv) decl
  modifyEnv (testExt.addEntry · {
    name := decl, run, isUnsafe := val.safety == .unsafe, file := ← getFileName, docstring?
  })

/-- Marks a definition as a test, discovered and run by the Errata test runner. -/
meta initialize
  registerBuiltinAttribute {
    ref := `Errata.test
    name := `test
    descr := "Marks a definition as a test, discovered and run by the Errata test runner."
    -- Applied after compilation so the declaration's docstring is in the environment to capture.
    applicationTime := .afterCompilation
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
A module to read tests from: the module itself, or, with a trailing {lit}`.*`, the module and every
imported module below it.
-/
syntax testModules := ident ("." "*")?

/--
{lit}`getAllTests% "package" Mod.A Mod.B.* ...` reads the tests recorded by {lit}`@[test]` in the
named modules, and expands to the array of {name}`TestEntry` values that run them. A name with a
trailing {lit}`.*` also names every imported module below it. Even if a module is named more than
once, its tests are not duplicated. Each module must be imported, with {lit}`import all` for
module-system modules, so its tests are reachable. Unsafe tests are wrapped in
{kw (of := Lean.Parser.Term.unsafe)}`unsafe`.
-/
syntax (name := getAllTests) "getAllTests%" str testModules* : term

/-- Expands {lit}`getAllTests%` by reading the recorded tests of the named modules. -/
@[term_elab getAllTests]
meta def elabGetAllTests : TermElab := fun stx expectedType? => do
  let `(getAllTests% $pkg:str $specs:testModules*) := stx
    | throwUnsupportedSyntax
  let package := pkg.getString
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let mut entries : Array Term := #[]
  -- A module may be named twice, or be selected by a name that ends in `.*`. Nonetheless, its tests
  -- are gathered only once.
  let mut seen : NameSet := {}
  for spec in specs do
    let (modStx, below) ← match spec with
      | `(testModules| $m:ident.*) => pure (m, true)
      | `(testModules| $m:ident) => pure (m, false)
      | _ => throwUnsupportedSyntax
    let rootName := modStx.getId
    let some rootIdx := env.getModuleIdx? rootName
      | throwErrorAt modStx "Module `{rootName}` is not imported, so its tests cannot be \
          reached. Import it, using `import all {rootName}` if it belongs to the module system."
    let mut chosen : Array (Name × ModuleIdx) := #[(rootName, rootIdx)]
    if below then
      for h : idx in [0 : moduleNames.size] do
        if rootName.isPrefixOf moduleNames[idx] then chosen := chosen.push (moduleNames[idx], idx)
    for (moduleName, idx) in chosen do
      if seen.contains moduleName then continue
      seen := seen.insert moduleName
      let moduleStr := moduleName.toString
      for test in testExt.getModuleEntries env idx do
        -- The internal name is used here, because the user-facing name can be ambiguous for private
        -- tests
        let userName := privateToUserName test.name
        let testName := testNameBelow moduleName userName
        let range ← findDeclarationRanges? test.name
        let location : Location := {
          file := test.file
          startPos := (range.map (·.range.pos)).getD ⟨0, 0⟩
          endPos := (range.map (·.range.endPos)).getD ⟨0, 0⟩
        }
        -- The docstring captured when the attribute was applied, so the report and widget can show it.
        let docStx ← match test.docstring? with
          | some doc => `(some $(quote doc))
          | none => `((none : Option String))
        let ref ← `(@$(mkCIdent test.run))
        let run ← if test.isUnsafe then `(unsafe $ref) else pure ref
        entries := entries.push <| ←
          `({ package := $(quote package), moduleName := $(quote moduleStr),
              test := $(quote testName), location := $(← exprToSyntax (toExpr location)),
              docstring? := $docStx, run := $run : Errata.TestEntry })
  elabTerm (← `(#[$entries,*])) expectedType?
