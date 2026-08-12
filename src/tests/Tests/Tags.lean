/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import VersoManual

set_option doc.verso true

namespace Verso.Tests.Tags

open Verso Genre Manual

/-! Tests for assigning user-chosen tags with {name}`providedTag`. -/

/--
Runs a traversal action against an empty state, returning its result, the resulting state, and
whether any errors were logged.
-/
private def run (act : StateT TraverseState (BuildLogT IO) α) : IO (α × TraverseState × Bool) := do
  let logger ← Logger.new
  let (result, state) ← (act.run (TraverseState.initialize {})).run logger
  let failed ← logger.failIfErrors
  return (result, state, failed != 0)

/-- The HTML id assigned to an element, if it has one. -/
private def htmlId (state : TraverseState) (id : InternalId) : Option String :=
  state.externalTags[id]?.map (·.htmlId.toString)

/-
A tag that nobody else holds is assigned exactly as written, and gives the element its HTML id.
-/
/-- info: (true, some "my-tag", false) -/
#guard_msgs in
#eval show IO _ from do
  let ((tag, id), state, failed) ← run do
    let id ← freshId
    let tag ← providedTag id #["page"] "my-tag"
    pure (tag, id)
  pure (tag.isSome, htmlId state id, failed)

/-
Assigning the same tag to the same element again is what later traversal rounds do, and is not an
error.
-/
/-- info: (true, some "my-tag", false) -/
#guard_msgs in
#eval show IO _ from do
  let ((tag, id), state, failed) ← run do
    let id ← freshId
    let _ ← providedTag id #["page"] "my-tag"
    let tag ← providedTag id #["page"] "my-tag"
    pure (tag, id)
  pure (tag.isSome, htmlId state id, failed)

/-
A tag that another element already holds is refused, and the element that asked for it is left
without an external tag.
-/
/--
info: Duplicate tag 'my-tag'
An error was encountered!
---
info: (false, some "my-tag", none, true)
-/
#guard_msgs in
#eval show IO _ from do
  let ((tag, first, second), state, failed) ← run do
    let first ← freshId
    let second ← freshId
    let _ ← providedTag first #["page"] "my-tag"
    let tag ← providedTag second #["page"] "my-tag"
    pure (tag, first, second)
  pure (tag.isSome, htmlId state first, htmlId state second, failed)

/-
A name that a machine-assigned tag already holds is refused for the same reason: both kinds of tag
draw on one set of names.
-/
/--
info: Duplicate tag 'my-tag'
An error was encountered!
---
info: (false, some "my-tag", none, true)
-/
#guard_msgs in
#eval show IO _ from do
  let ((tag, machine, chosen), state, failed) ← run do
    let machine ← freshId
    let chosen ← freshId
    let _ ← externalTag machine #["page"] "my-tag"
    let tag ← providedTag chosen #["page"] "my-tag"
    pure (tag, machine, chosen)
  pure (tag.isSome, htmlId state machine, htmlId state chosen, failed)

end Verso.Tests.Tags
