/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Environment

namespace Verso.Doc

open Lean

@[match_pattern]
private def versoModuleDocNameString : String := "the canonical document object name"

def docName (moduleName : Name) : Name :=
  id <| .str moduleName versoModuleDocNameString

/-- If the argument is a module's document name, extract the module name. Otherwise do nothing. -/
def unDocName (docName : Name) : Name :=
  match docName with
  | .str moduleName versoModuleDocNameString => moduleName
  | _ => docName

/-- info: `X.Y -/
#guard_msgs in
#eval unDocName <| docName `X.Y

/-- info: `X.Y -/
#guard_msgs in
#eval unDocName `X.Y

macro "%doc" moduleName:ident : term =>
  pure <| mkIdentFrom moduleName <| docName moduleName.getId

macro "%docName" moduleName:ident : term =>
  let n := mkIdentFrom moduleName (docName moduleName.getId) |>.getId
  pure <| quote n


def currentDocName [Monad m] [MonadEnv m] : m Name := do
  pure <| docName <| (← Lean.MonadEnv.getEnv).mainModule
