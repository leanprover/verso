/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio Jesus Gallego Arias
-/
import Lean.Elab.Command
import Verso.EnvExtension

namespace Verso.Tests.DocElabExtensions

/-!
This module defines a small test-only `LocalPersistentEnvExtension`.
`Define` adds one local entry, `Middle` imports `Define` without adding entries, and `Use` checks
that lookup in the final importer sees the entry while `Middle`'s serialized entries for this
extension are empty.
-/

open Lean Elab Command

private def addTestEntry (entries : Lean.NameMap (Array Name)) (key value : Name) :
    Lean.NameMap (Array Name) :=
  entries.insert key <| (entries.find? key |>.getD #[]).push value

private abbrev TestLocalExtension :=
  LocalPersistentEnvExtension (Name × Array Name) (Name × Name) (Lean.NameMap (Array Name))

initialize testLocalExt : TestLocalExtension ←
  LocalPersistentEnvExtension.register {
    name := `Verso.Tests.DocElabExtensions.testLocalExt
    mkInitialState := pure {}
    addImportedEntryFn
      | entries, (key, values) =>
        values.foldl (init := entries) fun entries value =>
          addTestEntry entries key value
    addEntryFn
      | entries, (key, value) =>
        addTestEntry entries key value
    exportEntriesFn _ entries :=
      .uniform entries.toArray
  }

def testLocalExtensionEntries (env : Environment) (key : Name) : Array Name :=
  testLocalExt.getState env |>.find? key |>.getD #[]

def testLocalExtensionModuleEntries (env : Environment) (moduleIdx : ModuleIdx) :
    Array (Name × Array Name) :=
  testLocalExt.getModuleEntries env moduleIdx

elab "#register_inherited_test_local_entry" : command => do
  modifyEnv fun env =>
    testLocalExt.addEntry env (`inheritedTestLocalExtension, `inheritedTestEntry)
