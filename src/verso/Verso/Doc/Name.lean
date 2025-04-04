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

/-- Treats an identifier as a module that contains Verso using the standard convention -/
macro "%doc" moduleName:ident : term =>
  pure <| mkIdentFrom moduleName <| docName moduleName.getId

/--
Treats an identifier as a module that contains Verso using the standard convention if it exists, or
uses the usual interpretation of the name otherwise.
-/
macro "%doc?" nameOrModuleName:ident : term => do
  let n := mkIdentFrom nameOrModuleName (docName nameOrModuleName.getId)
  let r ← Macro.resolveGlobalName n.getId
  let r := r.filter (·.2.isEmpty) -- ignore field access possibilities here
  if r.isEmpty then pure nameOrModuleName
  else pure n

macro "%docName" moduleName:ident : term =>
  let n := mkIdentFrom moduleName (docName moduleName.getId) |>.getId
  pure <| quote n

macro "%docName?" nameOrModuleName:ident : term => do
  let n := mkIdentFrom nameOrModuleName (docName nameOrModuleName.getId) |>.getId
  let r ← Macro.resolveGlobalName n
  let r := r.filter (·.2.isEmpty) -- ignore field access possibilities here
  pure <| quote <|
    if r.isEmpty then nameOrModuleName.getId
    else n


def currentDocName [Monad m] [MonadEnv m] : m Name := do
  pure <| docName <| (← Lean.MonadEnv.getEnv).mainModule
