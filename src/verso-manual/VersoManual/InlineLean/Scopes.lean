/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.Command
import Lean.Environment

open Lean Elab Command


namespace Verso.Genre.Manual.InlineLean.Scopes

initialize leanSampleScopes : Lean.EnvExtension (List Scope) ←
  Lean.registerEnvExtension (pure [])

def initScopes [Monad m] [MonadEnv m] [MonadOptions m] [MonadResolveName m] : m Unit := do
  if leanSampleScopes.getState (← getEnv) |>.isEmpty then
    let basicSc : Scope := {
        header :=  "",
        opts := ← getOptions,
        currNamespace := ← getCurrNamespace,
        openDecls := ← getOpenDecls
      }
    modifyEnv (leanSampleScopes.setState · [basicSc])

def getScopes [Monad m] [MonadEnv m] [MonadOptions m] [MonadResolveName m] : m (List Scope) := do
  initScopes
  return leanSampleScopes.getState (← getEnv)

def setScopes [Monad m] [MonadEnv m] (scopes : List Scope) : m Unit := do
  modifyEnv (leanSampleScopes.setState · scopes)

/--
Runs an elaborator action with the current namespace and open declarations that have been found via
inline Lean blocks.
-/
def runWithOpenDecls (act : TermElabM α) : TermElabM α := do
  let scope := (← getScopes).head!
  withTheReader Core.Context ({· with currNamespace := scope.currNamespace, openDecls := scope.openDecls}) do
    let initNames := (← getThe Term.State).levelNames
    try
      modifyThe Term.State ({· with levelNames := scope.levelNames})
      act
    finally
      modifyThe Term.State ({· with levelNames := initNames})

/--
Runs an elaborator action with the section variables that have been established via inline Lean code.

This is a version of `Lean.Elab.Command.runTermElabM`.
-/
def runWithVariables (elabFn : Array Expr → TermElabM α) : TermElabM α := do
  let scope := (← getScopes).head!
  Term.withAutoBoundImplicit do
    let msgLog ← Core.getMessageLog
    Term.elabBinders scope.varDecls fun xs => do
      -- We need to synthesize postponed terms because this is a checkpoint for the auto-bound implicit feature
      -- If we don't use this checkpoint here, then auto-bound implicits in the postponed terms will not be handled correctly.
      Term.synthesizeSyntheticMVarsNoPostponing
      let mut sectionFVars := {}
      for uid in scope.varUIds, x in xs do
        sectionFVars := sectionFVars.insert uid x
      withReader ({ · with sectionFVars := sectionFVars }) do
        -- We don't want to store messages produced when elaborating `(getVarDecls s)` because they have already been saved when we elaborated the `variable`(s) command.
        -- So, we use `Core.resetMessageLog`.
        Core.setMessageLog msgLog
        let someType := mkSort levelZero
        Term.addAutoBoundImplicits' xs someType fun xs _ =>
          Term.withoutAutoBoundImplicit <| elabFn xs
