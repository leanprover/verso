/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The `@[setting]` attribute, which records a declaration of type `Errata.Setting` in `settingExt` so
that tests can take it as a parameter.
-/
module

public import Errata.TestRegistry
public import Lean
public meta import Lean
public meta import Errata.TestRegistry

open Lean Meta Elab

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/--
Checks that a test executable can reach {name}`decl` through a plain {lit}`import` of its module.
In a module file, this holds for a public declaration, such as one in a {lit}`public section`.
-/
meta def ensureExported (decl : Name) : AttrM Unit := do
  unless ((← getEnv).setExporting true).contains decl do
    throwError m!"`{privateToUserName decl}` is private or not exported, so a test executable \
      cannot reach it. Make it public, for example by declaring it in a `public section`."

/--
Records a declaration as a setting and makes it reducible, so that instance resolution sees a test's
parameter {lit}`(x : S)` at the type of the setting's values. The declaration must be a runtime
definition of type {lit}`Errata.Setting`, exported with its value, with no universe parameters, and
marked as a setting once.
-/
meta def recordSetting (decl : Name) : AttrM Unit := do
  let env ← getEnv
  let known := settingExt.getState env
  if known.any (·.decl == decl) then
    throwError m!"`{privateToUserName decl}` is already marked as a setting"
  if isMarkedMeta env decl then
    throwError m!"A setting must not be `meta`"
  ensureExported decl
  let info ← getConstInfo decl
  unless info.levelParams.isEmpty do
    throwError m!"A setting must not be universe polymorphic"
  -- The structure is declared in a module that imports this one.
  let settingType := mkConst `Errata.Setting
  let fits ← (do isDefEq (← instantiateMVars info.type) settingType : MetaM Bool).run'
  unless fits do
    throwError m!"`@[setting]` requires the type `Errata.Setting`, and `{decl}` has the \
      type{indentExpr info.type}"
  match (env.setExporting true).find? decl with
  | some (.defnInfo _) => pure ()
  | _ =>
    throwError m!"`{decl}` must expose its value to the modules that import it, so that a test's \
      parameter has the setting's type there. Mark it `@[expose]`, or declare it with `abbrev`."
  setReducibilityStatus decl .reducible
  let docstring? ← findDocString? env decl
  modifyEnv (settingExt.addEntry · { decl, file := ← getFileName, docstring? })

/--
Marks a definition of type {lit}`Errata.Setting` as a setting, which tests take as parameters and the
configuration gives values. The declaration's fully qualified name is the setting's name.
-/
meta initialize
  registerBuiltinAttribute {
    ref := `Errata.setting
    name := `setting
    descr := "Marks a definition of type `Errata.Setting` as a setting, which tests take as \
      parameters."
    -- Applied after compilation so the declaration's docstring is in the environment to capture.
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `setting kind
      recordSetting decl
  }
