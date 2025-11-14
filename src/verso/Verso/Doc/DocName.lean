/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public meta import Lean.Environment

set_option doc.verso true

namespace Verso.Doc

open Lean

@[match_pattern]
private def versoModuleDocNameString : String := "the canonical document object name"

public def docName (moduleName : Name) : Name :=
  id <| .str moduleName versoModuleDocNameString
