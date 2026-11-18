/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import Verso

/-!
These tests check what a document contains when one of its elements fails to elaborate. A failure in
one inline or one nested block is reported at that element, which becomes empty, and the rest of its
block is in the document. A failure here means that one error removes more of the document than the
element that failed, or that an error is reported twice or not at all.

The documents are elaborated all at once with `#docs`, which runs the same elaborators for each
block as the `#doc` command. Each test shows the messages of the document, and most then show its
value.

In prior versions of Verso, an error in an element of a top-level block without a parse error
removed the whole top-level block from the document, and a header with a failing role opened no
part.
-/

namespace Verso.ElementErrorsTest

open Lean Elab Command
open Verso.Doc.Elab

/-- A role whose expander fails. -/
@[role]
def failing : RoleExpanderOf Unit
  | (), _ => throwError "The role fails."

/-- A role that logs a message and elaborates to nothing. -/
@[role]
def logged : RoleExpanderOf Unit
  | (), _ => do
    logInfo "The contents were elaborated."
    ``(Verso.Doc.Inline.concat #[])

/-- A directive whose expander fails before it elaborates its contents. -/
@[directive]
def failingDirective : DirectiveExpanderOf Unit
  | (), _ => throwError "The directive fails."

/-- A role that logs its own error and then aborts, as Lean's elaborators do. -/
@[role]
def aborting : RoleExpanderOf Unit
  | (), _ => do
    logError "The role reports its own error."
    throwAbortTerm

/--
A role whose expander throws the runtime exception that Lean throws when it runs out of heartbeats.
-/
@[role]
def outOfTime : RoleExpanderOf Unit
  | (), _ => do
    throw (.error (← getRef) (.tagged `runtime.maxHeartbeats m!"The roots ran out of time."))

/-
A header with a failing role opens its part. The part's title has the text around the role, and the
paragraph after the header is in the part.
-/

/--
error: The role fails.
-/
#test_msgs in
#docs (.none) headerWithFailingRole "Forest" :=
:::::::
# Oaks {failing}[and] Maples

Mycelium spreads under the trees.
:::::::

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Forest"]
  "Forest"
  none
  #[]
  #[Verso.Doc.Part.mk
      #[Verso.Doc.Inline.text "Oaks ", Verso.Doc.Inline.concat #[], Verso.Doc.Inline.text " Maples"]
      "Oaks  and  Maples"
      none
      #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "Mycelium spreads under the trees."]]
      #[]]
-/
#test_msgs in
#eval headerWithFailingRole.toPart

/-
A list keeps all its items when a block in one item fails. The failing block is empty, and the
blocks around it are kept. Description lists and blockquotes elaborate their blocks the same way.
-/

/--
error: The directive fails.
-/
#test_msgs in
#docs (.none) listWithFailingBlock "Leaves" :=
:::::::
* Leaves turn red in the fall.

* :::failingDirective
  :::

  Then they fall.

* Trees grow new leaves in spring.
:::::::

/--
info: #[Verso.Doc.Block.ul
    #[{ contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "Leaves turn red in the fall."]] },
      { contents := #[Verso.Doc.Block.concat #[], Verso.Doc.Block.para #[Verso.Doc.Inline.text "Then they fall."]] },
      { contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "Trees grow new leaves in spring."]] }]]
-/
#test_msgs in
#eval listWithFailingBlock.toPart.content

/-
The contents of a directive whose expander fails aren't elaborated in its place: the role in its
contents logs no message.
-/

/--
error: The directive fails.
-/
#test_msgs in
#docs (.none) failingDirectiveDoc "Mycelium" :=
:::::::
:::failingDirective
Mycelium {logged}[spreads] through the soil.
:::

Trees grow above it.
:::::::

/-
A role that logs its own error and then aborts is reported by that one message, and the rest of its
paragraph is kept.
-/

/--
error: The role reports its own error.
-/
#test_msgs in
#docs (.none) abortingRoleDoc "Bark" :=
:::::::
Trees {aborting}[] grow bark.
:::::::

/--
info: #[Verso.Doc.Block.para
    #[Verso.Doc.Inline.text "Trees ", Verso.Doc.Inline.concat #[], Verso.Doc.Inline.text " grow bark."]]
-/
#test_msgs in
#eval abortingRoleDoc.toPart.content

/-
A runtime exception in an element isn't caught at the element. It stops the elaboration of the
document, which is then not defined.
-/

/--
error: The roots ran out of time.
-/
#test_msgs in
#docs (.none) outOfTimeDoc "Roots" :=
:::::::
Roots {outOfTime}[] grow deep.
:::::::

/-- info: The document is defined: false -/
#test_msgs in
#eval show CommandElabM Unit from do
  let defined := (← getEnv).contains `Verso.ElementErrorsTest.outOfTimeDoc
  logInfo m!"The document is defined: {defined}"
