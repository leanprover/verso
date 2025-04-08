/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.Command
import Lean.Elab.Deriving.Basic

open Lean Elab Command Term
open Lean Parser Term

namespace Verso.Instances.Deriving

def deriveQuote (declNames : Array Name) : CommandElabM Bool := do
  let #[declName] := declNames
    | return false
  let env ← getEnv
  let some (.inductInfo ind) := env.find? declName
    | return false
  if ind.isRec then return false
  let mut branches : Array (TSyntax ``matchAlt) := #[]
  for ctorName in ind.ctors do
    let some (.ctorInfo ci) := env.find? ctorName
      | throwError "'{ctorName}' is not a constructor"
    let mut patvars := #[]
    for i in [0:ci.numParams + ci.numFields] do
      patvars := patvars.push (mkIdent s!"x{i}".toName)
    let lhs := Syntax.mkCApp ctorName patvars
    let rhs := Syntax.mkCApp ``Syntax.mkCApp #[quote ctorName, ← `(#[$[quote $patvars],*])]
    let alt ← `(matchAltExpr| | $lhs => $rhs)
    branches := branches.push alt
  let cmd ←
    `(instance : Quote $(mkIdent declName) where
        quote x :=
          match x with
          $branches:matchAlt*)
  elabCommand cmd
  return true

initialize
  registerDerivingHandler ``Quote deriveQuote
