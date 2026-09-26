/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Fixtures: resources that tests share, such as a built test project or a running server. Each fixture
is set up once per run, prepared before each test that uses it, and torn down once at the end. Tests
take fixtures as parameters, and `@[fixture]` records the declarations that declare them.
-/
module

public import Errata.TestM
public import Errata.Setting
public import Errata.TestRegistry
public import Lean
public meta import Lean
public meta import Errata.TestRegistry
public meta import Errata.SettingAttribute

open Lean Meta Elab

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/--
A fixture: a resource that tests share. Its {name (full := Fixture.setup)}`setup` runs once per run
and produces its value, which crosses between processes as the string that
{name (full := Fixture.toString)}`toString` makes of it and that
{name (full := Fixture.fromString)}`fromString` reads back.
{name (full := Fixture.prepare)}`prepare` runs before each test that uses the fixture, and
{name (full := Fixture.teardown)}`teardown` runs once at the end whenever the setup was invoked,
with the value when the setup produced one. Declarations of this type marked {lit}`@[fixture]`
declare fixtures, and their docstrings describe them.
-/
structure Fixture where
  /-- The type of the value that a test receives. -/
  type : Type
  /-- The string that stands for a value between processes. -/
  toString : type → String
  /-- Reads a value from its string, or rejects the string. -/
  fromString : String → Option type
  /-- Creates the resource and produces its value. -/
  setup : FixtureM type
  /-- Readies the resource for the next test that uses it. -/
  prepare : type → FixtureM Unit := fun _ => pure ()
  /--
  Removes the resource. It receives the value when the setup produced one, and {lean}`none` when the
  setup failed or was stopped, in which case it removes whatever the setup left behind.
  -/
  teardown : Option type → FixtureM Unit := fun _ => pure ()

/--
Fixtures stand for the types of their values, so a parameter {lit}`(x : F)` has the type
{lit}`F.type`.
-/
instance : CoeSort Fixture Type := ⟨Fixture.type⟩

/-!
Fixtures with parameters stand for the types of their values too, so a test's parameter
{lit}`(x : F)` has the value's type when {lit}`F` takes settings and fixtures. That type is the same
for every argument. Fixtures take up to eight parameters, and each parameter's type has an
{lit}`Inhabited` instance.
-/

instance [Inhabited α₁] : CoeSort (α₁ → Fixture) Type :=
  ⟨fun f => Fixture.type (f default)⟩

instance [Inhabited α₁] [Inhabited α₂] : CoeSort (α₁ → α₂ → Fixture) Type :=
  ⟨fun f => Fixture.type (f default default)⟩

instance [Inhabited α₁] [Inhabited α₂] [Inhabited α₃] : CoeSort (α₁ → α₂ → α₃ → Fixture) Type :=
  ⟨fun f => Fixture.type (f default default default)⟩

instance [Inhabited α₁] [Inhabited α₂] [Inhabited α₃] [Inhabited α₄] :
    CoeSort (α₁ → α₂ → α₃ → α₄ → Fixture) Type :=
  ⟨fun f => Fixture.type (f default default default default)⟩

instance [Inhabited α₁] [Inhabited α₂] [Inhabited α₃] [Inhabited α₄] [Inhabited α₅] :
    CoeSort (α₁ → α₂ → α₃ → α₄ → α₅ → Fixture) Type :=
  ⟨fun f => Fixture.type (f default default default default default)⟩

instance [Inhabited α₁] [Inhabited α₂] [Inhabited α₃] [Inhabited α₄] [Inhabited α₅]
    [Inhabited α₆] : CoeSort (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → Fixture) Type :=
  ⟨fun f => Fixture.type (f default default default default default default)⟩

instance [Inhabited α₁] [Inhabited α₂] [Inhabited α₃] [Inhabited α₄] [Inhabited α₅]
    [Inhabited α₆] [Inhabited α₇] : CoeSort (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → α₇ → Fixture) Type :=
  ⟨fun f => Fixture.type (f default default default default default default default)⟩

instance [Inhabited α₁] [Inhabited α₂] [Inhabited α₃] [Inhabited α₄] [Inhabited α₅]
    [Inhabited α₆] [Inhabited α₇] [Inhabited α₈] :
    CoeSort (α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → α₇ → α₈ → Fixture) Type :=
  ⟨fun f => Fixture.type (f default default default default default default default default)⟩

/--
Marks a test's use of a fixture as shared: tests that take {lit}`(x : shared F)` may run at the
same time as other shared users of {lit}`F`. {lean}`shared` is the identity on types, so
{lit}`x` has the type of the fixture's value, and {lit}`@[test]` reads a parameter of type
{lit}`shared F` as a shared claim on {lit}`F`.
-/
@[reducible, expose] def shared (α : Type) : Type := α

/--
The value of the fixture {name}`F`, named {name}`name`, among {name}`fixtures`: the last value given
for the name, parsed by the fixture's parser. If the name has no value, or the parser rejects its
value, the test or fixture phase ends with an error that names the fixture.
-/
def Fixture.withValue {m : Type → Type} {α : Type} [Monad m] [MonadExceptOf IO.Error m]
    (F : Fixture) (name : String) (fixtures : Array (String × String)) (k : F.type → m α) :
    m α := do
  let some raw := (fixtures.findRev? (·.1 == name)).map (·.2)
    | throwThe IO.Error <| .userError s!"the fixture {name} has no value"
  let some value := F.fromString raw
    | throwThe IO.Error <| .userError s!"the fixture {name} has the value {raw.quote}, which its \
        parser rejects"
  k value

/--
Runs one phase of the fixture {name}`F`, named {name}`name`. The setup's result is its value as a
string. The prepare requires {name}`own?`, the setup's value, and the teardown receives it when it
is present. If the fixture's parser rejects the value, the phase ends with an error that names the
fixture.
-/
def Fixture.runPhase (F : Fixture) (name : String) (phase : FixturePhase) (own? : Option String) :
    FixtureM (Option String) := do
  let parse (raw : String) : FixtureM F.type := do
    let some v := F.fromString raw
      | throwThe IO.Error <| .userError s!"the fixture {name} has the value {raw.quote}, which its \
          parser rejects"
    return v
  match phase with
  | .setup => return some (F.toString (← F.setup))
  | .prepare =>
    let some raw := own?
      | throwThe IO.Error <| .userError s!"the fixture {name}'s prepare needs its value, and it \
          received none"
    F.prepare (← parse raw)
    return none
  | .teardown =>
    F.teardown (← own?.mapM parse)
    return none

/-- A parameter of a test or a fixture: a setting, or a fixture that it uses. -/
inductive Parameter where
  /-- A setting that it takes. -/
  | setting (use : SettingUse)
  /--
  A fixture that it takes, exclusively or shared. {name}`fixture` is the fixture as the parameter's
  type names it, whose value's type is the parameter's type.
  -/
  | fixture (use : FixtureUse) (fixture : Expr)

/--
The use of the fixture that a parameter's type names, exclusive or shared, and the fixture as the
type names it. The type is read as elaborated: {lit}`(x : F)` has the type {lit}`Fixture.type F`,
{lit}`(x : shared F)` the type {lit}`shared (Fixture.type F)`, and a fixture with parameters appears
applied to default arguments.
-/
meta def fixtureOfParameter? (env : Environment) (type : Expr) : Option (FixtureUse × Expr) := do
  let (type, isShared) :=
    if type.isAppOfArity ``shared 1 then (type.appArg!, true) else (type, false)
  let .app (.const ``Errata.Fixture.type []) arg := type | none
  let .const f _ := arg.getAppFn | none
  unless (fixtureExt.getState env).any (·.name == f) do none
  return ({ decl := f, exclusive := !isShared }, arg)

/--
The setting that a parameter's type names: {lit}`S` for a parameter of type {lit}`S`, where
{lit}`S` is a declaration that {lit}`@[setting]` marks. The type is read as elaborated, where the
parameter {lit}`(x : S)` has the type {lit}`Setting.type S`. The use holds the setting's docstring
and declared default.
-/
meta def settingOfParameter? (env : Environment) (type : Expr) : Option SettingUse :=
  match type with
  | .app (.const ``Errata.Setting.type []) (.const s []) => settingUse? env s
  | _ => none

/-- The number of parameters that a fixture may take, one for each coercion to its value's type. -/
meta def maxParameters : Nat := 8

/-- What the parameters of a test or of a fixture may be, for messages about the others. -/
meta def parametersMessage (what : String) : String :=
  s!"{what} parameters are settings and fixtures: `S` for a declaration `S` marked `@[setting]`, \
    and `F` or `shared F` for a declaration `F` marked `@[fixture]`."

/--
Classifies the parameters of {name}`decl`, a test or a fixture (as {name}`what` says), as settings
and fixtures, with a message naming any other parameter and any fixture taken twice.
-/
meta def classifyParameters (decl : Name) (what : String) (params : Array Expr) :
    MetaM (Array Parameter) := do
  let env ← getEnv
  let userName := privateToUserName decl
  let mut out := #[]
  for p in params do
    let ty ← instantiateMVars (← inferType p)
    let localDecl ← p.fvarId!.getDecl
    match localDecl.binderInfo with
    | .instImplicit =>
      throwError m!"`{userName}` has an instance parameter of type{indentExpr ty}\n\
        {parametersMessage s!"A {what}'s"}"
    | .implicit | .strictImplicit =>
      throwError m!"The parameter `{localDecl.userName}` of `{userName}` is implicit. A {what}'s \
        parameters are explicit settings and fixtures. A setting named before its declaration \
        becomes an implicit parameter when `autoImplicit` is on, so declare the setting before the \
        {what}."
    | .default =>
      if let some use := settingOfParameter? env ty then
        out := out.push (.setting use)
      else if let some (use, fixture) := fixtureOfParameter? env ty then
        if out.any (fun | .fixture u _ => u.decl == use.decl | _ => false) then
          throwError m!"`{userName}` takes the fixture `{use.decl}` twice. A {what} takes each \
            fixture once, exclusively or shared."
        out := out.push (.fixture use fixture)
      else
        if let .app (.const ``Option _) inner := ty then
          if let some use := settingOfParameter? env inner then
            throwError m!"The parameter `{localDecl.userName}` of `{userName}` has the type \
              `Option {use.decl}`. A setting has a declared default or is mandatory, so a {what} \
              takes it as `{use.decl}`."
        -- Parameters whose types are definitions that stand for settings name the settings
        -- through other names.
        let named? : Option Name := match ty with
          | .app (.const ``Errata.Setting.type []) (.const c []) => some c
          | _ => none
        let alias? := named?.bind fun c =>
          match (env.find? c).bind (·.value?) with
          | some (.const s []) =>
            if (settingExt.getState env).any (·.decl == s) then some (c, s) else none
          | _ => none
        if let some (c, s) := alias? then
          throwError m!"The parameter `{localDecl.userName}` of `{userName}` has the type \
            `{c}`, which stands for the setting `{s}`. A {what} names a setting directly: \
            write `{s}`."
        throwError m!"The parameter `{localDecl.userName}` of `{userName}` has the \
          type{indentExpr ty}\nwhich is neither a setting nor a fixture. \
          {parametersMessage s!"A {what}'s"}"
  return out

/--
Wraps {name}`action`, which mentions the parameters {name}`params` and is an action of the monad
{name}`monad` with the result type {name}`result`, in the combinators that read each parameter's
value from {name}`settings` and {name}`fixtures`, from the innermost parameter outwards.
-/
meta def bindParameters (params : Array Expr) (uses : Array Parameter) (settings fixtures : Expr)
    (monad result action : Expr) : MetaM Expr := do
  let mut action := action
  for (p, u) in (params.zip uses).reverse do
    let lam ← mkLambdaFVars #[p] action
    let (combinator, value, name, pairs) := match u with
      | .setting use =>
        (``Setting.withValue, mkConst use.decl, settingNameOf use.decl, settings)
      | .fixture use fixture => (``Fixture.withValue, fixture, settingNameOf use.decl, fixtures)
    action ← mkAppOptM combinator
      #[some monad, some result, none, none, some value, some (toExpr name), some pairs, some lam]
  return action

/-- The type of name and value pairs, as the settings and the fixtures' values arrive. -/
meta def pairsType : Expr :=
  mkApp (mkConst ``Array [.zero])
    (mkApp2 (mkConst ``Prod [.zero, .zero]) (mkConst ``String) (mkConst ``String))

/--
The name for the definition that runs {name}`decl`: {lit}`run` below the declaration's own name, or
{lit}`run_2`, {lit}`run_3`, and so on when that name is taken.
-/
meta def runDeclName (env : Environment) (decl : Name) : Name := Id.run do
  let mut name := decl ++ `run
  let mut n := 2
  while env.contains name do
    name := decl ++ Name.mkSimple s!"run_{n}"
    n := n + 1
  return name

/--
Builds the definition that runs a phase of the fixture {name}`decl`, and returns its value with the
settings and the fixtures that the fixture takes. The definition receives the settings and the
fixtures' values as name and value pairs, the phase, and the fixture's own value, parses the values
of the fixture's parameters, applies the fixture to them, and runs the phase.
-/
meta def fixtureAction (decl : Name) : MetaM (Expr × Array SettingUse × Array Name) := do
  let info ← getConstInfo decl
  let userName := privateToUserName decl
  withLocalDeclD `settings pairsType fun settings =>
  withLocalDeclD `fixtures pairsType fun fixtures =>
  withLocalDeclD `phase (mkConst ``FixturePhase) fun phase =>
  withLocalDeclD `own (mkApp (mkConst ``Option [.zero]) (mkConst ``String)) fun own =>
  forallTelescope info.type fun params body => do
    unless ← isDefEq body (mkConst ``Errata.Fixture) do
      throwError m!"`@[fixture]` requires the type `Errata.Fixture`, after the fixture's \
        parameters, and `{userName}` has the type{indentExpr info.type}"
    let uses ← classifyParameters decl "fixture" params
    unless info.levelParams.isEmpty do
      throwError m!"A fixture must not be universe polymorphic"
    let mut settingUses := #[]
    let mut fixtureUses := #[]
    for u in uses do
      match u with
      | .setting use => settingUses := settingUses.push use
      | .fixture use _ =>
        unless use.exclusive do
          throwError m!"`{userName}` takes the fixture `{use.decl}` as `shared`, and `shared` has \
            no meaning on a fixture's parameters: tests claim fixtures, exclusively or shared. \
            Write `{use.decl}`."
        fixtureUses := fixtureUses.push use.decl
    -- A test's parameter has the type of the value of the fixture applied to default arguments, so
    -- each parameter's type needs an `Inhabited` instance.
    if params.size > maxParameters then
      throwError m!"`{userName}` has {params.size} parameters, and a fixture takes at most \
        {maxParameters}."
    for p in params do
      let ty ← inferType p
      if (← trySynthInstance (mkApp (mkConst ``Inhabited [.succ .zero]) ty)) matches .none then
        throwError m!"The parameter `{(← p.fvarId!.getDecl).userName}` of `{userName}` has the \
          type{indentExpr ty}\nwhich has no `Inhabited` instance. A fixture's parameters need one, \
          since a test's parameter stands for the fixture's value through the fixture applied to \
          default arguments."
    -- The value crosses between processes as a string, with the same type, printer, and parser
    -- whatever the parameters are.
    let applied := mkAppN (mkConst decl) params
    for field in [``Errata.Fixture.type, ``Errata.Fixture.toString, ``Errata.Fixture.fromString] do
      let value ← whnf (mkApp (mkConst field) applied)
      if (← instantiateMVars value).hasFVar then
        throwError m!"The field `{field.getString!}` of `{userName}` depends on its parameters. A \
          fixture's `type`, `toString`, and `fromString` are the same for every value of its \
          parameters."
    let action ← mkAppM ``Fixture.runPhase #[applied, toExpr (settingNameOf decl), phase, own]
    let action ← bindParameters params uses settings fixtures (mkConst ``FixtureM)
      (mkApp (mkConst ``Option [.zero]) (mkConst ``String)) action
    return (← mkLambdaFVars #[settings, fixtures, phase, own] action, settingUses, fixtureUses)

/--
Records a declaration as a fixture that asks for {name}`threads?` hardware threads, and makes it
reducible, so that a test's parameter {lit}`(x : F)` has the type of the fixture's value. The
declaration must be a runtime definition of type {lit}`Errata.Fixture` after
its parameters, exported with its value, with no universe parameters, and marked as a fixture once.
The definition that runs its phases is compiled into an exported definition beside it.
-/
meta def recordFixture (decl : Name) (threads? : Option Nat) : AttrM Unit := do
  let env ← getEnv
  if (fixtureExt.getState env).any (·.name == decl) then
    throwError m!"`{privateToUserName decl}` is already marked as a fixture"
  if isMarkedMeta env decl then
    throwError m!"A fixture must not be `meta`"
  ensureExported decl
  match (env.setExporting true).find? decl with
  | some (.defnInfo _) => pure ()
  | _ =>
    throwError m!"`{decl}` must expose its value to the modules that import it, so that a test's \
      parameter has the fixture's type there. Mark it `@[expose]`, or declare it with `abbrev`."
  if threads? == some 0 then
    throwError m!"A fixture asks for at least one thread"
  setReducibilityStatus decl .reducible
  let (action, settings, fixtures) ← (fixtureAction decl).run'
  let run := runDeclName (← getEnv) decl
  let type ← (do
    let result := mkApp (mkConst ``FixtureM) (mkApp (mkConst ``Option [.zero]) (mkConst ``String))
    mkArrow pairsType (← mkArrow pairsType (← mkArrow (mkConst ``FixturePhase)
      (← mkArrow (mkApp (mkConst ``Option [.zero]) (mkConst ``String)) result))) : MetaM Expr).run'
  let val ← mkDefinitionValInferringUnsafe run [] type action .opaque
  withExporting (isExporting := true) do
    addAndCompile (.defnDecl val)
  let docstring? ← findDocString? (← getEnv) decl
  modifyEnv (fixtureExt.addEntry · {
    name := decl, run, isUnsafe := val.safety == .unsafe, file := ← getFileName, docstring?,
    settings, fixtures, threads?
  })

/--
The arguments of the {lit}`fixture` attribute: {lit}`@[fixture]`, or
{lit}`@[fixture (threads := N)]` for a fixture whose phases ask for {lit}`N` hardware threads. When
tests run concurrently, each phase runs with {lit}`LEAN_NUM_THREADS` set to its thread grant, which
is one when the fixture asks for none, and the processes that the phase starts inherit it. Fixtures
whose setups run a Lake build therefore ask for the threads that the build should use.
-/
syntax (name := fixture) "fixture" (" (" &"threads" " := " num ")")? : attr

/--
Marks a definition of type {lit}`Errata.Fixture`, after its parameters, as a fixture, which tests
take as parameters. The declaration's fully qualified name is the fixture's name.
-/
meta initialize
  registerBuiltinAttribute {
    ref := `Errata.fixture
    name := `fixture
    descr := "Marks a definition of type `Errata.Fixture` as a fixture, which tests take as \
      parameters."
    -- Applied after compilation so the declaration's docstring is in the environment to capture.
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      let threads? ← match stx with
        | `(attr| fixture) => pure none
        | `(attr| fixture (threads := $n:num)) => pure (some n.getNat)
        | _ => throwUnsupportedSyntax
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `fixture kind
      recordFixture decl threads?
  }
