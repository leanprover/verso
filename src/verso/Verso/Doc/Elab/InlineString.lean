/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Verso.Doc.Elab.ExpanderAttribute
public import Lean.KeyedDeclsAttribute

namespace Verso.Doc.Elab
open Lean

public abbrev InlineToString := Environment → Syntax → Option String

initialize inlineToStringAttr : KeyedDeclsAttribute InlineToString ←
  mkUncheckedDocExpanderAttribute `inline_to_string ``InlineToString "Indicates that this function converts an inline element to a plain string for use in previews and navigation" `inlineToStringAttr

unsafe def inlineToStringForUnsafe (env : Environment) (x : Name) : Array InlineToString :=
  let expanders := inlineToStringAttr.getEntries env x
  expanders.map (·.value) |>.toArray

@[implemented_by inlineToStringForUnsafe]
opaque inlineToStringFor (env : Environment) (x : Name) : Array InlineToString

/-- Heuristically construct a plain string preview of the syntax of an inline element -/
public def inlineToString (env : Environment) (inline : Syntax) : String := Id.run do
  let kind := inline.getKind
  let toStr ← inlineToStringFor env kind
  for f in toStr do
    if let some str := f env inline then return str

  dbg_trace "Failed to convert {inline} with {kind}"

  fallback
where
  fallback := pure "<missing>"
