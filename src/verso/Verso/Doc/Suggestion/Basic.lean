/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Elab.InfoTree.Types
public import Lean.Elab.InfoTree.Main

namespace Verso.Doc.Suggestion

open Lean Elab

public structure Suggestion where
  summary : String
  replacement : String
deriving TypeName

public def saveSuggestion [Monad m] [MonadInfoTree m] (stx : Syntax) (summary replacement: String) : m Unit := do
  pushInfoLeaf <| .ofCustomInfo {stx := stx, value := Dynamic.mk (Suggestion.mk summary replacement) }
