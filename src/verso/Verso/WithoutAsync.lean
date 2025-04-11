/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.CoreM
import Lean.Data.Options
import Lean.Elab.Command

import SubVerso.Compat

open Lean Elab Command

namespace Verso

def commandWithoutAsync : (act : CommandElabM α) → CommandElabM α :=
  SubVerso.Compat.commandWithoutAsync

def withoutAsync [Monad m] [MonadWithOptions m] : (act : m α) → m α :=
  withOptions (Elab.async.set · false)
