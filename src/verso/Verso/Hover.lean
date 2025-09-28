/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Elab.InfoTree
public import Lean.Message

set_option doc.verso true

namespace Verso.Hover

open Lean Elab

/-!
Lean's built-in hover mechanism isn't particularly extensible, so {module -checked}`Verso.Doc.Lsp`
contains a number of custom handlers that use custom info tree entries to add Verso-related
features.

This module contains the underlying data representation used by these extensions, as well as
user-facing API for adding custom hover annotations.
-/

public inductive UserHover where
  /-- A Markdown string to send as the hover -/
  | markdown (markedString : String)
  | messageData (messageData : MessageData)

public def CustomHover.toString (hover : UserHover) : IO String :=
  match hover with
  | .markdown str => pure str
  | .messageData m => m.toString

public instance : Coe String UserHover where
  coe := .markdown

public instance : Coe MessageData UserHover where
  coe := .messageData

/-- A custom info node to save in the {name (full := Info.ofCustomInfo)}`ofCustomInfo` -/
public structure CustomHover where
  /-- A Markdown string to send as the hover -/
  markedString : String
deriving TypeName

public def addCustomHover [Monad m] [MonadInfoTree m] [MonadLiftT BaseIO m] (stx : Syntax) (hover : UserHover) : m Unit := do
  let txt ← match hover with
    | .markdown str => pure str
    | .messageData m => m.toString
  pushInfoLeaf <| .ofCustomInfo ⟨stx, .mk <| CustomHover.mk txt⟩
