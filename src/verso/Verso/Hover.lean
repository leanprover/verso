/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.InfoTree
import Lean.Message

namespace Verso.Hover

open Lean Elab

inductive UserHover where
  /-- A Markdown string to send as the hover -/
  | markdown (markedString : String)
  | messageData (messageData : MessageData)

def CustomHover.toString (hover : UserHover) : IO String :=
  match hover with
  | .markdown str => pure str
  | .messageData m => m.toString

instance : Coe String UserHover where
  coe := .markdown

instance : Coe MessageData UserHover where
  coe := .messageData

structure CustomHover where
  /-- A Markdown string to send as the hover -/
  markedString : String
deriving TypeName

def addCustomHover [Monad m] [MonadInfoTree m] [MonadLiftT BaseIO m] (stx : Syntax) (hover : UserHover) : m Unit := do
  let txt ← match hover with
    | .markdown str => pure str
    | .messageData m => m.toString
  pushInfoLeaf <| .ofCustomInfo ⟨stx, .mk <| CustomHover.mk txt⟩
