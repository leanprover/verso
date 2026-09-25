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
public import Errata.TestRegistry
public import Lean
public meta import Lean
public meta import Errata.TestRegistry
public meta import Errata.SettingAttribute
public meta import Errata.NameJson
public meta import Errata.Widget

open Lean Meta Elab Term

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/--
The setting that a parameter's type names: {lit}`S` for a parameter of type {lit}`S` and
{lit}`Option S`, where {lit}`S` is a declaration that {lit}`@[setting]` marks. The type is read as
elaborated, where the parameter {lit}`(x : S)` has the type {lit}`Setting.type S`.
-/
meta def settingOfParameter? (env : Environment) (type : Expr) : Option SettingUse :=
  let known (e : Expr) : Option Name :=
    match e with
    | .app (.const ``Errata.Setting.type []) (.const s []) =>
      if (settingExt.getState env).any (·.decl == s) then some s else none
    | _ => none
  match type with
  | .app (.const ``Option _) inner => (known inner).map ({ decl := ·, optional := true })
  | _ => (known type).map ({ decl := ·, optional := false })

/--
Builds the action that runs a declaration as a test, using the {name}`IsTest` instance for its type
that is visible at the declaration, and returns it with the settings that the test takes. Every
parameter of the declaration is a setting {lit}`S` or {lit}`Option S`. The action receives the
settings as name and value pairs, parses each parameter's value with its setting's parser, and
applies the test to the values. The declaration must be a runtime declaration with no universe
parameters.
-/
meta def testAction (decl : Name) : MetaM (Expr × Array SettingUse) := do
  let env ← getEnv
  if isMarkedMeta env decl then
    throwError m!"A test must not be `meta`"
  let info ← getConstInfo decl
  let testName := privateToUserName decl
  let pairs := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``String) (mkConst ``String)
  let settingsType := mkApp (mkConst ``Array [.zero]) pairs
  withLocalDeclD `settings settingsType fun settings => do
    forallTelescope info.type fun params body => do
      let mut uses : Array SettingUse := #[]
      for p in params do
        let ty ← instantiateMVars (← inferType p)
        let localDecl ← p.fvarId!.getDecl
        match localDecl.binderInfo with
        | .instImplicit =>
          throwError m!"`{testName}` has an instance parameter of type{indentExpr ty}\nA test's \
            parameters are settings: `S` or `Option S` for a declaration `S` marked `@[setting]`."
        | .implicit | .strictImplicit =>
          throwError m!"The parameter `{localDecl.userName}` of `{testName}` is implicit. A \
            test's parameters are explicit settings. A setting named before its declaration \
            becomes an implicit parameter when `autoImplicit` is on, so declare the setting \
            before the test."
        | .default =>
          match settingOfParameter? env ty with
          | some use => uses := uses.push use
          | none =>
            -- Parameters whose types are definitions that stand for settings name the settings
            -- through other names.
            let named? : Option Name := match ty with
              | .app (.const ``Errata.Setting.type []) (.const c [])
              | .app (.const ``Option _) (.app (.const ``Errata.Setting.type []) (.const c [])) =>
                some c
              | _ => none
            let alias? := named?.bind fun c =>
              match (env.find? c).bind (·.value?) with
              | some (.const s []) =>
                if (settingExt.getState env).any (·.decl == s) then some (c, s) else none
              | _ => none
            if let some (c, s) := alias? then
              throwError m!"The parameter `{localDecl.userName}` of `{testName}` has the type \
                `{c}`, which stands for the setting `{s}`. A test names a setting directly: \
                write `{s}`."
            throwError m!"The parameter `{localDecl.userName}` of `{testName}` has the \
              type{indentExpr ty}\nwhich is not a setting. A test's parameters are settings: \
              `S` or `Option S` for a declaration `S` marked `@[setting]`."
      unless info.levelParams.isEmpty do
        throwError m!"A test must not be universe polymorphic"
      let goal := mkApp (mkConst ``IsTest) body
      let inst ← match ← trySynthInstance goal with
        | .some inst => instantiateMVars inst
        | _ =>
          throwError m!"`@[test]` requires an `Errata.IsTest` instance for the test's \
            type{indentExpr body}"
      let mut action := mkApp3 (mkConst ``IsTest.toTest) body inst (mkAppN (mkConst decl) params)
      -- The parameters are bound from the innermost outwards, each by the combinator that reads its
      -- setting's value.
      for i in (List.range params.size).reverse do
        let use := uses[i]!
        let combinator := if use.optional then ``Setting.withOptional else ``Setting.withValue
        action := mkApp4 (mkConst combinator) (mkConst use.decl)
          (toExpr (settingNameOf use.decl)) settings (← mkLambdaFVars #[params[i]!] action)
      return (← mkLambdaFVars #[settings] action, uses)

/--
The name for the definition that runs the test {name}`decl`: {lit}`run` below the test's own name,
or {lit}`run_2`, {lit}`run_3`, and so on when that name is taken.
-/
meta def runDeclName (env : Environment) (decl : Name) : Name := Id.run do
  let mut name := decl ++ `run
  let mut n := 2
  while env.contains name do
    name := decl ++ Name.mkSimple s!"run_{n}"
    n := n + 1
  return name

/--
Records a declaration as a test with the given tags. The action that runs it is compiled, with the
{name}`IsTest` instance in force here, into an exported definition beside it. Test executables
reach that definition through a plain {lit}`import` of the test's module. Tests must themselves be
exported: in a module, they are public, which a {lit}`public section` arranges. Docstrings are
read here, from the live environment, and stored with each test.
-/
meta def recordTest (decl : Name) (tags : Array String := #[]) : AttrM Unit := do
  if (testExt.getState (← getEnv)).any (·.name == decl) then
    throwError m!"`{privateToUserName decl}` is already marked as a test"
  ensureExported decl
  let (action, settings) ← (testAction decl).run'
  let run := runDeclName (← getEnv) decl
  let pairs := mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``String) (mkConst ``String)
  let type ← mkArrow (mkApp (mkConst ``Array [.zero]) pairs) (mkApp (mkConst ``TestM) (mkConst ``Unit))
  let val ← mkDefinitionValInferringUnsafe run [] type action .opaque
  withExporting (isExporting := true) do
    addAndCompile (.defnDecl val)
  let docstring? ← findDocString? (← getEnv) decl
  modifyEnv (testExt.addEntry · {
    name := decl, run, isUnsafe := val.safety == .unsafe, file := ← getFileName, docstring?,
    tags, settings
  })

/--
The arguments of the {lit}`test` attribute: {lit}`@[test]`, or {lit}`@[test (tags := a, b)]` with the
test's tags.
-/
syntax (name := test) "test" (" (" ident " := " ident,+ ")")? : attr

/-- The tags that the attribute's syntax gives. The one keyword argument is {lit}`tags`. -/
meta def testTags (stx : Syntax) : AttrM (Array String) := do
  match stx with
  | `(attr| test) => return #[]
  | `(attr| test ($key := $tags,*)) =>
    unless key.getId == `tags do
      throwErrorAt key m!"`@[test]` has no argument `{key.getId}`; its one argument is `tags`"
    return (tags.getElems.map (·.getId.toString (escape := false)))
  | _ => throwUnsupportedSyntax

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

/-- The declared default of the setting {name}`decl`, read from the setting's value. -/
private meta unsafe def settingDefaultImpl (decl : Name) : MetaM (Option String) :=
  evalExpr (Option String) (mkApp (mkConst ``Option [.zero]) (mkConst ``String))
    (mkApp (mkConst ``Errata.Setting.default?) (mkConst decl)) (safety := .unsafe)

@[implemented_by settingDefaultImpl, inherit_doc settingDefaultImpl]
private meta opaque settingDefault (decl : Name) : MetaM (Option String)

/--
A setting that a test takes, as the widget offers a field for it: its name, whether it is optional,
its docstring, and its declared default, or {lean}`none` in its place when evaluating it fails.
-/
meta def declaredSetting (use : SettingUse) : AttrM Errata.Widget.DeclaredSetting := do
  let description? :=
    (settingExt.getState (← getEnv)).find? (·.decl == use.decl) |>.bind (·.docstring?)
  let default? ← try (settingDefault use.decl).run' catch _ => pure none
  return { name := settingNameOf use.decl, optional := use.optional, description?, default? }

/-- Marks a definition as a test, discovered and run by the Errata test runner. -/
meta initialize
  registerBuiltinAttribute {
    ref := `Errata.test
    name := `test
    descr := "Marks a definition as a test, discovered and run by the Errata test runner."
    -- Applied after compilation so the declaration's docstring is in the environment to capture.
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      let tags ← testTags stx
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `test kind
      recordTest decl tags
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
        settings := ← (test?.map (·.settings)).getD #[] |>.mapM declaredSetting
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
{lit}`getAllTests% "package" Mod.A Mod.B.* ...` reads the tests recorded by {lit}`@[test]` in the
named modules, and expands to the array of {name}`TestEntry` values that run them. A name with a
trailing {lit}`.*` also names every imported module below it. Even if a module is named more than
once, its tests are not duplicated. Each module must be imported so its tests are reachable. Each
test is named by its fully qualified declaration name, and its entry lists its tags and the settings
it takes, each with its description and a reference to its declared default. Unsafe tests are
wrapped in {kw (of := Lean.Parser.Term.unsafe)}`unsafe`.
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
        -- Each setting's description is its docstring, and its default is read from the setting's
        -- value when the test executable runs.
        let settings ← test.settings.mapM fun use => do
          let doc? := (settingExt.getState env).find? (·.decl == use.decl) |>.bind (·.docstring?)
          let docStx ← match doc? with
            | some doc => `(some $(quote doc))
            | none => `((none : Option String))
          `({ name := $(quote (settingNameOf use.decl)), optional := $(quote use.optional),
              description? := $docStx, default? := Errata.Setting.default? @$(mkCIdent use.decl)
              : Errata.SettingRef })
        entries := entries.push <| ←
          `({ package := $(quote package), moduleName := $(quote moduleStr),
              name := $(quote testName), path := $(quote path),
              location := $(← exprToSyntax (toExpr location)),
              docstring? := $docStx, tags := $(quote test.tags),
              settings := #[$settings,*], run := $run : Errata.TestEntry })
  elabTerm (← `(#[$entries,*])) expectedType?

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
