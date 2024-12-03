/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Server.CodeActions

namespace Verso.Doc

open Lean Elab Server RequestM

structure PointOfInterest where
  title : String

deriving TypeName

def PointOfInterest.save [Monad m] [MonadInfoTree m] (stx : Syntax) (title : String) : m Unit := do
  pushInfoLeaf <| .ofCustomInfo {stx := stx, value := Dynamic.mk (PointOfInterest.mk title)}
