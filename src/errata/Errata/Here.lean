/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.Result
public meta import Lean

open Lean Elab Term

public section

set_option doc.verso true

/--
`here%` elaborates to the {name}`Errata.Location` of its own occurrence. Used as a default argument
(`by exact here%`), it is elaborated at each call site, so it captures the caller's position.
-/
syntax (name := hereStx) "here%" : term

@[term_elab hereStx]
meta def elabHere : TermElab := fun _stx _expectedType? => do
  let ref ← getRef
  let fileMap ← getFileMap
  let startPos := fileMap.toPosition (ref.getPos?.getD 0)
  let endPos := fileMap.toPosition (ref.getTailPos?.getD (ref.getPos?.getD 0))
  let file ← getFileName
  elabTerm (← `(Errata.Location.mk $(quote file)
      (Errata.Position.mk $(quote startPos.line) $(quote startPos.column))
      (Errata.Position.mk $(quote endPos.line) $(quote endPos.column)))) none
