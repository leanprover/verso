/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Fixtures: resources that tests share, such as a built test project or a running server. A fixture is
set up once per run, prepared before each test that uses it, and torn down once at the end. Tests
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
{lit}`(x : F)` has the value's type when {lit}`F` takes settings and fixtures. The type is that of
the fixture applied to default arguments, which is the same for every argument. Instance resolution
indexes a type by unfolding reducible definitions only, and it reaches the value's type through the
fixture, which is reducible, without unfolding the default arguments. Fixtures take up to eight
parameters.
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
Marks a test's use of a fixture as shared: a test that takes {lit}`(x : shared F)` may run at the
same time as other shared users of {lit}`F`. The fixture {lit}`F` stands for the type of its value,
and to Lean, {lean}`shared` is the identity on types, so {lit}`shared F` is the same type.
-/
@[reducible, expose] def shared (α : Type) : Type := α

/--
The value of the fixture {name}`F`, named {name}`name`, among {name}`fixtures`: the last value given
for the name, parsed by the fixture's parser. With no value, or a value that the parser rejects, the
test or fixture phase ends with an error that names the fixture.
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
string. The prepare receives {name}`own?`, the value from the setup, which it needs; the teardown
receives it when it is given. A value that the fixture's parser rejects ends the phase with an error
that names the fixture.
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
The fixture that a parameter's type names, and whether the use is exclusive, with the fixture as the
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

/-- What the parameters of a test or of a fixture may be, for messages about the others. -/
meta def parametersMessage (what : String) : String :=
  s!"{what} parameters are settings and fixtures: `S` or `Option S` for a declaration `S` marked \
    `@[setting]`, and `F` or `shared F` for a declaration `F` marked `@[fixture]`."

/--
Classifies the parameters of {name}`decl`, a test or a fixture (as {name}`what` says), as settings
and fixtures, with a message naming any other parameter.
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
        out := out.push (.fixture use fixture)
      else
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
        (if use.optional then ``Setting.withOptional else ``Setting.withValue, mkConst use.decl,
          settingNameOf use.decl, settings)
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
    -- The value's type crosses between processes as the type of every value, so it is the same
    -- whatever the parameters are.
    let applied := mkAppN (mkConst decl) params
    let valueType ← whnf (mkApp (mkConst ``Errata.Fixture.type) applied)
    if valueType.hasFVar then
      throwError m!"The type of `{userName}`'s value depends on its parameters. A fixture's \
        `type`, `toString`, and `fromString` are the same for every value of its parameters."
    let action ← mkAppM ``Fixture.runPhase #[applied, toExpr (settingNameOf decl), phase, own]
    let action ← bindParameters params uses settings fixtures (mkConst ``FixtureM)
      (mkApp (mkConst ``Option [.zero]) (mkConst ``String)) action
    return (← mkLambdaFVars #[settings, fixtures, phase, own] action, settingUses, fixtureUses)

/--
Records a declaration as a fixture that asks for {name}`threads?` hardware threads, and makes it
reducible, so that instance resolution sees a test's parameter {lit}`(x : F)` at the type of the
fixture's value. The declaration must be a runtime definition of type {lit}`Errata.Fixture` after
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
  let info ← getConstInfo decl
  unless info.levelParams.isEmpty do
    throwError m!"A fixture must not be universe polymorphic"
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
{lit}`@[fixture (threads := N)]` for a fixture whose phases ask for {lit}`N` hardware threads.
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
