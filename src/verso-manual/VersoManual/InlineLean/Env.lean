/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Environment
import Lean.Exception
import Verso.Doc.Elab.Monad

open Lean
open Verso Doc Elab DocElabM

namespace Verso.Genre.Manual.InlineLean

def envParameter : Name := decl_name%

variable [Monad m] [MonadError m] [MonadReaderOf DocElabContext m] [MonadWithReaderOf DocElabContext m]
variable [MonadEnv m] [MonadFinally m] [MonadLiftT (ST IO.RealWorld) m] [MonadLiftT BaseIO m]

structure EnvRef where
  val : IO.Ref Environment

deriving instance TypeName for EnvRef

/--
If a special examples environment is specified, use it.
-/
def usingExamplesEnv (act : m α) : m α := do
  if let some (envRef : EnvRef) := (← parameterValue? envParameter) then
    let env ← envRef.val.get
    let realEnv ← getEnv
    try
      modifyEnv (fun _ => env)
      try
        act
      finally
        let env' ← getEnv
        envRef.val.set env'
    finally
      modifyEnv (fun _ => realEnv)
  else act

def getExamplesEnv : m Environment := do
  if let some (envRef : EnvRef) := (← parameterValue? envParameter) then
    envRef.val.get
  else getEnv

/--
Run `act` with the examples environment set to the current environment for rollback.
-/
def withIsolatedExamplesEnv (act : m α) : m α := do
  let env ← getExamplesEnv
  let ref ← IO.mkRef env
  let envRef := EnvRef.mk ref
  withParameter envParameter envRef act
