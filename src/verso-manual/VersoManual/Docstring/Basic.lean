/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Lean.Data.Options
public import Lean.DocString
public import Lean.Log
public import SubVerso.Highlighting.Highlighted
public import VersoManual.Docstring.Config
meta import Verso.Instances.Deriving

open Lean
open SubVerso.Highlighting

namespace Verso.Genre.Manual

public def getDocString?
    [Monad m] [MonadLiftT IO m] [MonadOptions m] [MonadLog m] [AddMessageContext m]
    (env : Environment) (declName : Name) :
    m (Option String) := do
  let docs? ← findDocString? env declName
  if docs?.isNone then
    if !(← Verso.Genre.Manual.Docstring.getAllowMissing) then
      Lean.logError m!"'{declName}' is not documented.\n\nSet option 'verso.docstring.allowMissing' to 'true' to allow missing docstrings."
    else
      Lean.logWarning m!"'{declName}' is not documented.\n\nSet option 'verso.docstring.allowMissing' to 'false' to disallow missing docstrings."
  return docs?


public structure Signature where
  /-- The signature formatted for wider screens, such as desktop displays -/
  wide : Highlighted
  /-- The signature formatted for narrower screens, such as mobile displays -/
  narrow : Highlighted
deriving ToJson, FromJson, Quote
