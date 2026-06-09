/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio Jesus Gallego Arias
-/
module
public import Lean.Environment

namespace Verso

open Lean

/-
`LocalPersistentEnvExtension` wraps a persistent extension whose state is split into a complete
lookup state and a local export delta.

Imported entries initialize only the complete lookup state. Local entries update both states. Export
receives only the local delta, so the extension cannot accidentally re-serialize transitive imported
entries.

This is the same persistence discipline as `SimplePersistentEnvExtension`, staged for extension
shapes where the serialized entry type and the added entry type differ. The complete lookup state and
local export delta intentionally have the same type here. Extensions that need different state types,
async support, or replay support should use `PersistentEnvExtension` directly.

Imported entries are eagerly folded into the complete lookup state when the module is imported. This
matches the existing Verso doc-expander lookup pattern, where document elaboration repeatedly queries
the complete map by key. Extensions whose import-time initialization cost matters more than direct
lookup should use `PersistentEnvExtension` directly and keep a custom serialized representation.
-/
public structure LocalPersistentEnvExtension (α β σ : Type) where
  private ext : PersistentEnvExtension α β (σ × σ)
deriving Inhabited

namespace LocalPersistentEnvExtension

public structure Descr (α β σ : Type) where
  name : Name := by exact decl_name%
  mkInitialState : IO σ
  addImportedEntryFn : σ → α → σ
  addEntryFn : σ → β → σ
  exportEntriesFn : Environment → σ → OLeanEntries (Array α)

public def register {α β σ : Type} [Inhabited σ]
    (descr : Descr α β σ) :
    IO (LocalPersistentEnvExtension α β σ) := do
  let ext ← registerPersistentEnvExtension {
    name := descr.name
    mkInitial := do
      pure (← descr.mkInitialState, ← descr.mkInitialState)
    addImportedFn := fun entrySets => do
      let mut state ← descr.mkInitialState
      for entries in entrySets do
        for entry in entries do
          state := descr.addImportedEntryFn state entry
      pure (state, ← descr.mkInitialState)
    addEntryFn := fun (state, delta) entry =>
      (descr.addEntryFn state entry, descr.addEntryFn delta entry)
    exportEntriesFnEx := fun env (_, delta) =>
      descr.exportEntriesFn env delta
    asyncMode := .mainOnly
  }
  pure { ext }

public def getState {α β σ : Type} [Inhabited σ]
    (ext : LocalPersistentEnvExtension α β σ) (env : Environment) : σ :=
  match ext with
  | ⟨rawExt⟩ => (PersistentEnvExtension.getState rawExt env).1

public def addEntry {α β σ : Type} (ext : LocalPersistentEnvExtension α β σ)
    (env : Environment) (entry : β) : Environment :=
  match ext with
  | ⟨rawExt⟩ => PersistentEnvExtension.addEntry rawExt env entry

public def getModuleEntries {α β σ : Type} [Inhabited σ]
    (ext : LocalPersistentEnvExtension α β σ) (env : Environment) (moduleIdx : ModuleIdx)
    (level := OLeanLevel.exported) : Array α :=
  match ext with
  | ⟨rawExt⟩ => PersistentEnvExtension.getModuleEntries (level := level) rawExt env moduleIdx
