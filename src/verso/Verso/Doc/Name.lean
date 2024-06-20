/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Environment

namespace Verso.Doc

open Lean

def docName (moduleName : Name) : Name :=
  id <| .str moduleName "the canonical document object name"

macro "%doc" moduleName:ident : term =>
  pure <| mkIdentFrom moduleName <| docName moduleName.getId

macro "%docName" moduleName:ident : term =>
  let n := mkIdentFrom moduleName (docName moduleName.getId) |>.getId
  pure <| quote n


def currentDocName [Monad m] [MonadEnv m] : m Name := do
  pure <| docName <| (← Lean.MonadEnv.getEnv).mainModule
