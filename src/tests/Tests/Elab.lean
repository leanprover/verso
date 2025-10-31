/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
import Verso
import VersoManual
namespace Verso.BlocksTest
open Genre Manual InlineLean

/-
This test case answers the question "why do we need to allow metavariables of unknown type when we
walk the expression in `Verso.Doc.Elab.findTypeclassInstances`?"

The custom role gives rise to three metavariables that are unresolved until
`Term.synthesizeSyntheticMVarsNoPostponing` runs:
 - X : Type
 - Y : OfNat X 4
 - Z : ToString X
-/
section
open Lean
open Doc.Elab

@[role]
def insertSyntaxGivingRiseToMetavariables : RoleExpanderOf Unit
  | (), _ => do
    ``(Doc.Inline.text s!"{4}")

#docs (.none) mvar1 "blah" :=
:::::::
I can {insertSyntaxGivingRiseToMetavariables}[]
:::::::

@[role]
def totallyUndefined : RoleExpanderOf Unit
  | (), _content => do
    `(_)

-- This is not a good error message and it would be great to improve it!
-- However, the right way to do this may be to eliminate these fallback functions.
/--
error: don't know how to synthesize placeholder for argument `head`
context:
docReconInBlock✝ : Doc.DocReconstruction
⊢ Doc.Inline Doc.Genre.none
-/
#guard_msgs in
#docs (.none) var8 "My title here" :=
:::::::
Attempting to insert something {totallyUndefined}[]
:::::::
end

#guard_msgs in
#docs (Manual) novar "My title here" :=
:::::::
A variable like {lean +error}`x`.
:::::::

section
variable (x : Int)
#docs (Manual) var2 "My title here" :=
:::::::
A variable like {lean}`x`.
:::::::
end

#docs (Manual) mvar3 "My title here" :=
:::::::
A variable like {lean}`(_ : Nat)`.
:::::::

#docs (Manual) mvar4 "My title here" :=
:::::::
A variable like {lean}`_`.
:::::::
