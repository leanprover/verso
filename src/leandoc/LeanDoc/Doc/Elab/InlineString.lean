/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean
import LeanDoc.Doc.Elab.ExpanderAttribute

namespace LeanDoc.Doc.Elab
open Lean

abbrev InlineToString := Environment → Syntax → Option String

initialize inlineToStringAttr : KeyedDeclsAttribute InlineToString ←
  mkDocExpanderAttribute `inline_to_string ``InlineToString "Indicates that this function converts an inline element to a plain string for use in previews and navigation" `inlineToStringAttr

unsafe def inlineToStringForUnsafe (env : Environment) (x : Name) : Array InlineToString :=
  let expanders := inlineToStringAttr.getEntries env x
  expanders.map (·.value) |>.toArray

@[implemented_by inlineToStringForUnsafe]
opaque inlineToStringFor (env : Environment) (x : Name) : Array InlineToString

/-- Heuristically construct a plan string preview of the syntax of an inline element -/
def inlineToString (env : Environment) (inline : Syntax) : String := Id.run do
  match inline with
  | stx@(.node _ kind _) =>
    let toStr ← inlineToStringFor env kind
    for f in toStr do
      if let some str := f env stx then return str
    fallback
  | _ =>
    fallback
where
  fallback := pure "<missing>"
