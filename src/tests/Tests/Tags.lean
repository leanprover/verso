/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import VersoManual
meta import VersoManual

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

/-
A name containing a space gives the element its slug as an HTML id.
-/
/-- info: (true, some "some-tag", false) -/
#guard_msgs in
#eval show IO _ from do
  let ((tag, id), state, failed) ← run do
    let id ← freshId
    let tag ← providedTag id #["page"] "some tag"
    pure (tag, id)
  pure (tag.isSome, htmlId state id, failed)

/-
Names that share a slug are duplicates, because both need the same HTML id. The error names the
slug when it differs from the name as written.
-/
/--
info: Duplicate tag 'some tag': its slug 'some-tag' is already in use
An error was encountered!
---
info: (false, some "some-tag", none, true)
-/
#guard_msgs in
#eval show IO _ from do
  let ((tag, first, second), state, failed) ← run do
    let first ← freshId
    let second ← freshId
    let _ ← providedTag first #["page"] "some-tag"
    let tag ← providedTag second #["page"] "some tag"
    pure (tag, first, second)
  pure (tag.isSome, htmlId state first, htmlId state second, failed)

/--
info: Duplicate tag 'some-tag'
An error was encountered!
---
info: (false, some "some-tag", none, true)
-/
#guard_msgs in
#eval show IO _ from do
  let ((tag, first, second), state, failed) ← run do
    let first ← freshId
    let second ← freshId
    let _ ← providedTag first #["page"] "some tag"
    let tag ← providedTag second #["page"] "some-tag"
    pure (tag, first, second)
  pure (tag.isSome, htmlId state first, htmlId state second, failed)

/-! Tests for assigning tags to parts with {name}`tagPart`. -/

/--
Runs a traversal action with no extensions against an empty state and context, returning its
result, the resulting state, and whether any errors were logged.
-/
private def runTraverse (act : TraverseM α) : IO (α × TraverseState × Bool) := do
  let logger ← Logger.new
  let (result, state) ←
    (TraverseM.run (ExtensionImpls.fromLists [] []) {} (TraverseState.initialize {}) act).run logger
  let failed ← logger.failIfErrors
  return (result, state, failed != 0)

/-
Traversal registers a part in the section domain under its name exactly as written, resolvable by
{name}`TraverseState.resolveDomainObject`, while its HTML id is the slug. The name in the part's
metadata is untouched.
-/
/-- info: (some "some tag", some "some-tag", true, some "some-tag", false) -/
#guard_msgs in
#eval show IO _ from do
  let ((name, id), state, failed) ← runTraverse do
    let id ← freshId
    let md : PartMetadata := { tag := some "some tag", id := some id }
    let part : Doc.Part Manual := .mk #[Doc.Inline.text "Some Tag"] "Some Tag" (some md) #[] #[]
    -- Two rounds, as the traversal driver would run them
    let t ← tagPart part md (·.id) (·.xrefTag) (·.tag) savePartXref
    let md := { md with xrefTag := some t }
    let _ ← tagPart part md (·.id) (·.xrefTag) (·.tag) savePartXref
    pure (md.tag, id)
  let resolved :=
    match state.resolveDomainObject sectionDomain "some tag" with
    | .ok link => some link.htmlId.toString
    | .error _ => none
  pure (name, htmlId state id,
    (state.getDomainObject? sectionDomain "some-tag").isNone, resolved, failed)

/-
Two parts that claim the same name produce a single, readable duplicate error.
-/
/--
info: Duplicate tag 'some tag': its slug 'some-tag' is already in use
An error was encountered!
---
info: true
-/
#guard_msgs in
#eval show IO _ from do
  let (_, _, failed) ← runTraverse do
    let first ← freshId
    let md1 : PartMetadata := { tag := some "some tag", id := some first }
    let part1 : Doc.Part Manual := .mk #[Doc.Inline.text "A"] "A" (some md1) #[] #[]
    let _ ← tagPart part1 md1 (·.id) (·.xrefTag) (·.tag) savePartXref
    let second ← freshId
    let md2 : PartMetadata := { tag := some "some tag", id := some second }
    let part2 : Doc.Part Manual := .mk #[Doc.Inline.text "B"] "B" (some md2) #[] #[]
    let _ ← tagPart part2 md2 (·.id) (·.xrefTag) (·.tag) savePartXref
  pure failed

/-! Tests for suggesting alternatives to unresolved cross-references. -/

/-- info: "" -/
#guard_msgs in
#eval suggestRefTargets #["alpha", "beta"] "zzzzzzzzzzzz"

/-- info: "\nDid you mean one of these?\n * 'some tag'\n * 'some-tag'" -/
#guard_msgs in
#eval suggestRefTargets #["some-tag", "some tag", "other"] "some tg"

/-
At most five targets are suggested.
-/
/-- info: "\nDid you mean one of these?\n * 'tag1'\n * 'tag2'\n * 'tag3'\n * 'tag4'\n * 'tag5'" -/
#guard_msgs in
#eval suggestRefTargets #["tag6", "tag5", "tag4", "tag3", "tag2", "tag1"] "tag"

/-! Tests for the unresolved-reference error message with {name}`unresolvedRefMessage`. -/

/-
A name that is absent from the domain gets suggestions of nearby names.
-/
/--
info: "No destination found for tag 'some tg' in Verso.Genre.Manual.section\nDid you mean one of these?\n * 'some tag'"
-/
#guard_msgs in
#eval show IO _ from do
  let (_, state, _) ← runTraverse do
    let id ← freshId
    modify (·.saveDomainObject sectionDomain "some tag" id)
  pure (unresolvedRefMessage state none "some tg")

/-
A name that is present in the domain failed to resolve for another reason, which the message
states instead of suggesting the name to itself.
-/
/--
info: "Ref some tag in Verso.Genre.Manual.section has 2 targets, can only link to one"
-/
#guard_msgs in
#eval show IO _ from do
  let (_, state, _) ← runTraverse do
    let first ← freshId
    let second ← freshId
    modify (·.saveDomainObject sectionDomain "some tag" first
      |>.saveDomainObject sectionDomain "some tag" second)
  pure (unresolvedRefMessage state none "some tag")

/-
A name whose domain object has no targets at all, which happens when only data was saved for it.
-/
/--
info: "No link target registered for some tag in Verso.Genre.Manual.section"
-/
#guard_msgs in
#eval show IO _ from do
  let (_, state, _) ← runTraverse do
    modify (·.saveDomainObjectData sectionDomain "some tag" .null)
  pure (unresolvedRefMessage state none "some tag")

end Verso.Tests.Tags
