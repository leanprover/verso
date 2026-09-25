/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.IsTest
public import Errata.Runner
public import Errata.Helpers
public import Errata.Setting
public import Errata.Fixture
public import Errata.TestRegistry
public import Lean
public meta import Lean
public meta import Errata.TestRegistry
public meta import Errata.SettingAttribute
public meta import Errata.Fixture
public meta import Errata.NameJson
public meta import Errata.Widget

open Lean Meta Elab Term

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/--
Builds the action that runs a declaration as a test, using the {name}`IsTest` instance for its type
that is visible at the declaration, and returns it with the settings and the fixtures that the test
takes. Every parameter of the declaration is a setting {lit}`S` or {lit}`Option S`, or a fixture
{lit}`F` or {lit}`shared F`. The action receives the settings and the fixtures' values as name and
value pairs, parses each parameter's value with its setting's or its fixture's parser, and applies
the test to the values. The declaration must be a runtime declaration with no universe parameters.
-/
meta def testAction (decl : Name) : MetaM (Expr × Array SettingUse × Array FixtureUse) := do
  let env ← getEnv
  if isMarkedMeta env decl then
    throwError m!"A test must not be `meta`"
  let info ← getConstInfo decl
  withLocalDeclD `settings pairsType fun settings =>
  withLocalDeclD `fixtures pairsType fun fixtures => do
    forallTelescope info.type fun params body => do
      let uses ← classifyParameters decl "test" params
      unless info.levelParams.isEmpty do
        throwError m!"A test must not be universe polymorphic"
      let goal := mkApp (mkConst ``IsTest) body
      let inst ← match ← trySynthInstance goal with
        | .some inst => instantiateMVars inst
        | _ =>
          throwError m!"`@[test]` requires an `Errata.IsTest` instance for the test's \
            type{indentExpr body}"
      let action := mkApp3 (mkConst ``IsTest.toTest) body inst (mkAppN (mkConst decl) params)
      let action ← bindParameters params uses settings fixtures (mkConst ``TestM) (mkConst ``Unit)
        action
      let settingUses := uses.filterMap fun | .setting u => some u | _ => none
      let fixtureUses := uses.filterMap fun | .fixture u _ => some u | _ => none
      return (← mkLambdaFVars #[settings, fixtures] action, settingUses, fixtureUses)

/--
Records a declaration as a test with the given tags and thread request. The action that runs it is
compiled, with the {name}`IsTest` instance in force here, into an exported definition beside it.
Test executables reach that definition through a plain {lit}`import` of the test's module. Tests
must themselves be exported: in a module, they are public, which a {lit}`public section` arranges.
Docstrings are read here, from the live environment, and stored with each test, together with the
fixtures that the test reaches, so that a test executable lists the test from its record alone.
-/
meta def recordTest (decl : Name) (tags : Array String := #[]) (threads? : Option Nat := none) :
    AttrM Unit := do
  if (testExt.getState (← getEnv)).any (·.name == decl) then
    throwError m!"`{privateToUserName decl}` is already marked as a test"
  ensureExported decl
  let (action, settings, fixtures) ← (testAction decl).run'
  let run := runDeclName (← getEnv) decl
  let type ← mkArrow pairsType
    (← mkArrow pairsType (mkApp (mkConst ``TestM) (mkConst ``Unit)))
  let val ← mkDefinitionValInferringUnsafe run [] type action .opaque
  withExporting (isExporting := true) do
    addAndCompile (.defnDecl val)
  let docstring? ← findDocString? (← getEnv) decl
  let reachedFixtures :=
    reachedFixtureDecls (fixtureExt.getState (← getEnv)) (fixtures.map (·.decl))
  modifyEnv (testExt.addEntry · {
    name := decl, run, isUnsafe := val.safety == .unsafe, file := ← getFileName, docstring?,
    tags, threads?, settings, fixtures, reachedFixtures
  })

/--
A value of a keyword argument of the {lit}`test` attribute: a name, such as a tag, or a number.
-/
syntax testArgValue := ident <|> num

/-- A keyword argument of the {lit}`test` attribute, such as {lit}`(tags := a, b)`. -/
syntax testArg := " (" ident " := " testArgValue,+ ")"

/--
The arguments of the {lit}`test` attribute: {lit}`@[test]`, or with keyword arguments, such as
{lit}`@[test (tags := a, b) (threads := 4)]` for a test with two tags that asks for four hardware
threads.
-/
syntax (name := test) "test" testArg* : attr

/--
The tags and the thread request that the attribute's syntax gives, from its keyword arguments
{lit}`tags` and {lit}`threads`.
-/
meta def testArgs (stx : Syntax) : AttrM (Array String × Option Nat) := do
  let `(attr| test $args:testArg*) := stx | throwUnsupportedSyntax
  let mut tags := #[]
  let mut threads? := none
  for arg in args do
    let `(testArg| ($key := $vals,*)) := arg | throwUnsupportedSyntax
    match key.getId with
    | `tags =>
      for v in vals.getElems do
        match v with
        | `(testArgValue| $i:ident) => tags := tags.push (i.getId.toString (escape := false))
        | _ => throwErrorAt v m!"`tags` takes names"
    | `threads =>
      match vals.getElems with
      | #[v] =>
        match v with
        | `(testArgValue| $n:num) =>
          if n.getNat == 0 then throwErrorAt n m!"A test asks for at least one thread"
          threads? := some n.getNat
        | _ => throwErrorAt v m!"`threads` takes a number"
      | _ => throwErrorAt key m!"`threads` takes one number"
    | other =>
      throwErrorAt key m!"`@[test]` has no argument `{other}`; its arguments are `tags` and \
        `threads`"
  return (tags, threads?)

/-- A synthetic syntax carrying the given source range, used to position the widget. -/
meta def rangeSyntax [Monad m] [MonadFileMap m]
    (startPos stopPos : String.Pos.Raw) : m Syntax := do
  let str := (← getFileMap).source
  let leading : Substring.Raw := { str, startPos, stopPos := startPos }
  let trailing : Substring.Raw := { str, startPos := stopPos, stopPos }
  return Syntax.atom (.original leading startPos trailing stopPos) ""

/-- How many lines above the marker's line the command around the marker is looked for. -/
private meta def commandSearchLines : Nat := 20

/--
The range of the command around {name}`pos`, found by parsing a command from the start of each line
at or above {name}`pos`'s own, up to {name}`commandSearchLines` above it. A parse that succeeds and
reaches past {name}`pos` is the command that {name}`pos` is in, and a parse from further up that ends
where that one does is the same command with its doc comment or its attribute list, so it gives the
range that the command begins at.
-/
private meta def commandAround (pos : String.Pos.Raw) : AttrM (Option Lean.Syntax.Range) := do
  let fileMap ← getFileMap
  let inputCtx := Parser.mkInputContext fileMap.source (← getFileName)
  let pmctx : Parser.ParserModuleContext := { env := ← getEnv, options := ← getOptions }
  let line := (fileMap.toPosition pos).line
  let mut found : Option Lean.Syntax.Range := none
  for back in [0:min commandSearchLines line] do
    let lineStart := fileMap.ofPosition ⟨line - back, 0⟩
    let (cmdStx, _, messages) := Parser.parseCommand inputCtx pmctx { pos := lineStart } {}
    if messages.hasErrors then continue
    let some range := cmdStx.getRange? | continue
    unless range.start ≤ pos && pos < range.stop do continue
    match found with
    | none => found := some range
    | some inner =>
      -- A parse that ends elsewhere is the command around this one, so there is nothing further up
      -- to find.
      if range.stop != inner.stop then break
      found := some range
  return found

/--
The source range to show the test's widget over: the whole command that marks the test, including a
doc comment above it. The command is re-parsed around the marker. Falls back to the marker itself,
which is also the range for a declaration from another module, marked with {lit}`attribute [test]`.
-/
meta def widgetRangeSyntax (decl : Name) (attrStx : Syntax) : AttrM Syntax := do
  -- The declaration ranges of an imported declaration are positions in its own module's file.
  if ((← getEnv).getModuleIdxFor? decl).isSome then return attrStx
  let some attrPos := attrStx.getPos? | return attrStx
  match ← commandAround attrPos with
  | some range => rangeSyntax range.start range.stop
  | none => return attrStx

/--
A setting that a test takes, as the widget offers a field for it: its name, whether it is optional,
its docstring, and its declared default.
-/
meta def declaredSetting (use : SettingUse) : Errata.Widget.DeclaredSetting :=
  { name := settingNameOf use.decl, optional := use.optional, description? := use.description?,
    default? := use.default? }

/-- Marks a definition as a test, discovered and run by the Errata test runner. -/
meta initialize
  registerBuiltinAttribute {
    ref := `Errata.test
    name := `test
    descr := "Marks a definition as a test, discovered and run by the Errata test runner."
    -- Applied after compilation so the declaration's docstring is in the environment to capture.
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      let (tags, threads?) ← testArgs stx
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `test kind
      recordTest decl tags threads?
      -- The widget reaches the editor through the info tree, which the language server keeps and a
      -- build leaves out, so a build skips the work of placing the widget.
      unless (← getInfoState).enabled do return
      -- The widget is shown while the cursor is anywhere in the declaration, its docstring included.
      let widgetStx ← widgetRangeSyntax decl stx
      -- A hash of the test's source, so a run is invalidated when the test is edited.
      let source := (← getFileMap).source
      let version := match widgetStx.getRange? with
        | some range =>
          let sub : Substring.Raw := { str := source, startPos := range.start, stopPos := range.stop }
          toString sub.toString.hash
        | none => ""
      -- In the language server, a run of the test's previous source ends as the edited test is
      -- elaborated, and the widget learns the test's place and settings. The place is the test's
      -- declaration range when it has one already, and otherwise the command that marks it, which
      -- is the same range for a test marked where it is declared.
      let test? := (testExt.getState (← getEnv)).find? (·.name == decl)
      let declared? ← test?.mapM testLocation
      let fileMap ← getFileMap
      let commandLocation? : Option Location := widgetStx.getRange?.map fun range => {
        file := test?.map (·.file) |>.getD "",
        startPos := fileMap.toPosition range.start, endPos := fileMap.toPosition range.stop }
      Errata.Widget.noteTest decl {
        version
        location? := declared?.filter (·.endPos.line != 0) <|> commandLocation?
        settings := (test?.map (·.settings)).getD #[] |>.map declaredSetting
        module := ← getMainModule
        file := (test?.map (·.file)).getD ""
        tags := (test?.map (·.tags)).getD #[]
      }
      let props := pure <| json% {
        decl: $(Errata.nameToJson decl),
        module: $(Errata.nameToJson (← getMainModule)),
        name: $(toString (privateToUserName decl)),
        version: $version
      }
      Lean.Widget.savePanelWidgetInfo Errata.Widget.runTestWidget.javascriptHash.val props widgetStx
  }

/-- The type of a helper, {lean}`List String → IO UInt32`. -/
meta def helperType : Expr :=
  mkForall `args .default (mkApp (mkConst ``List [.zero]) (mkConst ``String))
    (mkApp (mkConst ``IO) (mkConst ``UInt32))

/--
Records a declaration as a helper. The declaration must have the type {lean}`List String → IO UInt32`,
must be exported as a test is, and must not be {lit}`meta`, {lit}`noncomputable`, or universe
polymorphic. The helper's record holds its file and its docstring, read here from the live
environment.
-/
meta def recordHelper (decl : Name) : AttrM Unit := do
  if (helperExt.getState (← getEnv)).any (·.name == decl) then
    throwError m!"`{privateToUserName decl}` is already marked as a test helper"
  if isMarkedMeta (← getEnv) decl then
    throwError m!"A test helper must not be `meta`"
  if isNoncomputable (← getEnv) decl then
    throwError m!"A test helper must not be `noncomputable`"
  ensureExported decl
  let info ← getConstInfo decl
  unless info.levelParams.isEmpty do
    throwError m!"A test helper must not be universe polymorphic"
  let fits ← (do isDefEq (← instantiateMVars info.type) helperType : MetaM Bool).run'
  unless fits do
    throwError m!"`@[test_helper]` requires the type `List String → IO UInt32`, and \
      `{privateToUserName decl}` has the type{indentExpr info.type}"
  let docstring? ← findDocString? (← getEnv) decl
  modifyEnv (helperExt.addEntry · {
    name := decl, isUnsafe := info.isUnsafe, file := ← getFileName, docstring?
  })

/--
Marks a definition as a test helper: a function that a test runs as a subprocess of its own test
executable with {name}`runHelper`.
-/
meta initialize
  registerBuiltinAttribute {
    ref := `Errata.testHelper
    name := `test_helper
    descr := "Marks a definition as a test helper, which a test runs as a subprocess of its own \
      test executable."
    -- Applied after compilation so the declaration's docstring is in the environment to capture.
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `test_helper kind
      recordHelper decl
  }

/--
A module to read tests from: the module itself, or, with a trailing {lit}`.*`, the module and every
imported module below it.
-/
syntax testModules := ident ("." "*")?

/--
The settings that a test or fixture takes, as a test executable's entries list them: each with its
docstring as its description and its declared default, as {lit}`@[setting]` recorded them.
-/
meta def settingRefs (uses : Array SettingUse) : TermElabM (Array Term) :=
  uses.mapM fun use => do
    let quoteOpt (s? : Option String) : TermElabM Term := match s? with
      | some s => `(some $(quote s))
      | none => `((none : Option String))
    `({ name := $(quote (settingNameOf use.decl)), optional := $(quote use.optional),
        description? := $(← quoteOpt use.description?), default? := $(← quoteOpt use.default?)
        : Errata.SettingRef })

/--
{lit}`getAllTests% "package" Mod.A Mod.B.* ...` reads the tests recorded by {lit}`@[test]` in the
named modules, and expands to the array of {name}`TestEntry` values that run them. A name with a
trailing {lit}`.*` also names every imported module below it. Even if a module is named more than
once, its tests are not duplicated. Each module must be imported so its tests are reachable. Each
test is named by its fully qualified declaration name, and its entry lists its tags, the settings it
takes, each with its description and its declared default, and the fixtures it takes, each exclusive
or shared. Unsafe tests are wrapped in {kw (of := Lean.Parser.Term.unsafe)}`unsafe`.
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
          reached. Import it."
    let mut chosen : Array (Name × ModuleIdx) := #[(rootName, rootIdx)]
    if below then
      for h : idx in [0 : moduleNames.size] do
        if rootName.isPrefixOf moduleNames[idx] then chosen := chosen.push (moduleNames[idx], idx)
    for (moduleName, idx) in chosen do
      if seen.contains moduleName then continue
      seen := seen.insert moduleName
      let moduleStr := moduleName.toString
      for test in testExt.getModuleEntries env idx do
        let userName := privateToUserName test.name
        let testName := userName.toString
        let path := userName.components.map (·.toString (escape := false)) |>.toArray
        let location ← testLocation test
        -- The docstring captured when the attribute was applied, so the report and widget can show it.
        let docStx ← match test.docstring? with
          | some doc => `(some $(quote doc))
          | none => `((none : Option String))
        let ref ← `(@$(mkCIdent test.run))
        let run ← if test.isUnsafe then `(unsafe $ref) else pure ref
        let settings ← settingRefs test.settings
        let fixtures ← test.fixtures.mapM fun use =>
          `({ name := $(quote (settingNameOf use.decl)), exclusive := $(quote use.exclusive)
              : Errata.FixtureRef })
        let threadsStx ← match test.threads? with
          | some n => `(some $(quote n))
          | none => `((none : Option Nat))
        entries := entries.push <| ←
          `({ package := $(quote package), moduleName := $(quote moduleStr),
              name := $(quote testName), path := $(quote path),
              location := $(← exprToSyntax (toExpr location)),
              docstring? := $docStx, tags := $(quote test.tags), threads? := $threadsStx,
              settings := #[$settings,*], fixtures := #[$fixtures,*], run := $run
              : Errata.TestEntry })
  elabTerm (← `(#[$entries,*])) expectedType?

/--
{lit}`getAllFixtures%` reads the fixtures recorded by {lit}`@[fixture]` in every imported module,
and expands to the array of {name}`FixtureEntry` values that run their phases, in an order in which
each fixture follows the fixtures it takes. Each fixture is named by its fully qualified declaration
name, and its entry lists the settings and fixtures it takes and the threads it asks for. Unsafe
fixtures are wrapped in {kw (of := Lean.Parser.Term.unsafe)}`unsafe`.
-/
syntax (name := getAllFixtures) "getAllFixtures%" : term

/-- Expands {lit}`getAllFixtures%` by reading the recorded fixtures of the imported modules. -/
@[term_elab getAllFixtures]
meta def elabGetAllFixtures : TermElab := fun stx expectedType? => do
  let `(getAllFixtures%) := stx
    | throwUnsupportedSyntax
  let env ← getEnv
  let mut entries : Array Term := #[]
  for f in fixtureExt.getState env do
    let ref ← `(@$(mkCIdent f.run))
    let run ← if f.isUnsafe then `(unsafe $ref) else pure ref
    let range ← findDeclarationRanges? f.name
    let location : Location := {
      file := f.file
      startPos := (range.map (·.range.pos)).getD ⟨0, 0⟩
      endPos := (range.map (·.range.endPos)).getD ⟨0, 0⟩
    }
    let docStx ← match f.docstring? with
      | some doc => `(some $(quote doc))
      | none => `((none : Option String))
    let threadsStx ← match f.threads? with
      | some n => `(some $(quote n))
      | none => `((none : Option Nat))
    let settings ← settingRefs f.settings
    let deps := f.fixtures.map settingNameOf
    entries := entries.push <| ←
      `({ name := $(quote (settingNameOf f.name)), location := $(← exprToSyntax (toExpr location)),
          docstring? := $docStx, settings := #[$settings,*], fixtures := $(quote deps),
          threads? := $threadsStx, run := $run : Errata.FixtureEntry })
  elabTerm (← `((#[$entries,*] : Array Errata.FixtureEntry))) expectedType?

/--
{lit}`getAllHelpers%` reads the helpers recorded by {lit}`@[test_helper]` in every imported module,
and expands to the array of {name}`Helper` values that run them, each named by its fully qualified
declaration name. Unsafe helpers are wrapped in {kw (of := Lean.Parser.Term.unsafe)}`unsafe`.
-/
syntax (name := getAllHelpers) "getAllHelpers%" : term

/-- Expands {lit}`getAllHelpers%` by reading the recorded helpers of the imported modules. -/
@[term_elab getAllHelpers]
meta def elabGetAllHelpers : TermElab := fun stx expectedType? => do
  let `(getAllHelpers%) := stx
    | throwUnsupportedSyntax
  let env ← getEnv
  let mut entries : Array Term := #[]
  for idx in [0 : env.allImportedModuleNames.size] do
    for helper in helperExt.getModuleEntries env idx do
      let ref ← `(@$(mkCIdent helper.name))
      let run ← if helper.isUnsafe then `(unsafe $ref) else pure ref
      entries := entries.push <| ←
        `({ name := $(quote helper.name.toString), run := $run : Errata.Helper })
  elabTerm (← `((#[$entries,*] : Array Errata.Helper))) expectedType?
