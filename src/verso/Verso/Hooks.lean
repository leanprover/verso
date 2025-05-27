/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Environment
import Verso.Doc.Elab.Monad

open Lean

namespace Verso.Doc.Elab

private initialize documentFinishedHookExt : PersistentEnvExtension Name Name NameSet ← registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn _ := pure {}
    addEntryFn := NameSet.insert
    exportEntriesFn xs := xs.toArray.qsort (Name.quickCmp · · |>.isLT)
  }

abbrev DocumentFinishedHook := DocElabM Unit

initialize document_finished_hook : Unit ← registerBuiltinAttribute {
  name := `document_finished_hook,
  descr := "A hook to be executed when a Verso document completes elaboration",
  applicationTime := .afterCompilation
  add declName stx k := do
    unless k matches .global do
      throwError "The attribute `document_finished_hook` may only have global scope."
    if let some v := (← getEnv).findConstVal? declName then
      let t : Expr := .const ``DocumentFinishedHook []
      if v.type == t then
        modifyEnv (documentFinishedHookExt.addEntry · declName)
      else
        throwError "Expected a '{t}', got '{v.type}'"
    else
      throwError "'{declName}' not found"
}

private unsafe def documentFinishedHooksUnsafe [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] : m (Array DocumentFinishedHook) := do
  let hooks := documentFinishedHookExt.toEnvExtension.getState (← getEnv)
  let hooks := hooks.importedEntries.push (hooks.state.toArray) |>.flatten
  hooks.mapM (evalConst DocumentFinishedHook)

@[implemented_by documentFinishedHooksUnsafe]
opaque documentFinishedHooks [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] : m (Array DocumentFinishedHook)
