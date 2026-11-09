/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Errata
public import VersoManual
meta import Lean.Elab.Frontend
meta import VersoManual

/-!
These tests are for `linter.verso.manual.headerTags`. This linter warns about headers that don't
have a metadata block with an explicit `tag` field. A failure means that the linter doesn't warn on
a header that it should or that the editor's warnings after an edit differ from those of a build
from scratch.

In prior versions of Verso, this linter parsed commands one at a time and could show stale warnings
when a metadata block was edited.
-/

namespace Verso.Tests.VersoManual.HeaderTags

open Lean Elab Command Language

/--
Elaborates `input` as commands in the current environment, with the header tag linter enabled,
reusing the results of the commands of `old?` that are unchanged.
-/
meta def elabInput (input : String) (old? : Option IncrementalState) :
    CommandElabM IncrementalState := do
  -- Lean's command-line driver sets `internal.cmdlineSnapshots`. With it set, snapshots don't keep
  -- commands' syntax, so no command is reused.
  let opts := (← getOptions).setBool `internal.cmdlineSnapshots false
    |>.setBool `linter.verso.manual.headerTags true
  IO.processCommandsIncrementally (Parser.mkInputContext input "Input.lean") {}
    (Command.mkState (← getEnv) {} opts) old?

/-- The messages of all commands of `st`, each with its position and its full text. -/
meta def messages (st : IncrementalState) : IO (Array String) :=
  (toSnapshotTree st.initialSnap).getAll.flatMap (·.diagnostics.msgLog.toArray) |>.mapM fun m =>
    return s!"{m.pos.line}:{m.pos.column} {← m.data.toString}"

meta def firstLines (msgs : Array String) : List String :=
  msgs.toList.map fun m => (m.takeWhile (· != '\n')).copy

/-
The warning about a header disappears when a metadata block with a `tag` field is added after the
header and comes back when the block is removed. The messages of each version of the text equal
those of an elaboration from scratch.

In prior versions of the Manual genre, the linter checked the text after the header while linting
the header's command. An edit of the next block doesn't elaborate that command again, so the warning
stayed after the tag was added.
-/
/--
info: without a tag: [7:0 Missing permalink tag]; as from scratch: true
with a tag: []; as from scratch: true
without a tag again: [7:0 Missing permalink tag]; as from scratch: true
-/
#test_msgs in
run_cmd do
  let header := "#doc (Verso.Genre.Manual) \"Trees\" =>\n\n%%%\ntag := \"trees\"\n%%%\n\n\
    # Leaves\n\n"
  let untagged := header ++ "Leaves fall.\n"
  let tagged := header ++ "%%%\ntag := \"leaves\"\n%%%\n\nLeaves fall.\n"
  let mut old? := none
  let mut out := #[]
  for (name, text) in [("without a tag", untagged), ("with a tag", tagged),
      ("without a tag again", untagged)] do
    let edited ← elabInput text old?
    let msgs ← messages edited
    let fromScratch ← messages (← elabInput text none)
    out := out.push s!"{name}: {firstLines msgs}; as from scratch: {msgs == fromScratch}"
    old? := some edited
  logInfo ("\n".intercalate out.toList)

/-
The linter warns on a header that is the last block of a `#doc` document.
-/
/-- info: [9:0 Missing permalink tag] -/
#test_msgs in
run_cmd do
  let input := "#doc (Verso.Genre.Manual) \"Trees\" =>\n\n%%%\ntag := \"trees\"\n%%%\n\n\
    Trees grow.\n\n# Leaves\n"
  logInfo s!"{firstLines (← messages (← elabInput input none))}"

/-
The linter warns on a header that is followed by a deeper header. The deeper header has a tag.
-/
/-- info: [7:0 Missing permalink tag] -/
#test_msgs in
run_cmd do
  let input := "#doc (Verso.Genre.Manual) \"Trees\" =>\n\n%%%\ntag := \"trees\"\n%%%\n\n\
    # Leaves\n\n## Red\n\n%%%\ntag := \"red\"\n%%%\n\nMaple leaves turn red.\n"
  logInfo s!"{firstLines (← messages (← elabInput input none))}"

/-
The linter warns on a header that is followed by a header two levels higher. The other headers have
tags.
-/
/-- info: [19:0 Missing permalink tag] -/
#test_msgs in
run_cmd do
  let input := "#doc (Verso.Genre.Manual) \"Trees\" =>\n\n%%%\ntag := \"trees\"\n%%%\n\n\
    # Leaves\n\n%%%\ntag := \"leaves\"\n%%%\n\n## Red\n\n%%%\ntag := \"red\"\n%%%\n\n\
    ### Maple\n\n# Bark\n\n%%%\ntag := \"bark\"\n%%%\n\nBark is rough.\n"
  logInfo s!"{firstLines (← messages (← elabInput input none))}"

/-
The warning about the document's title disappears when a metadata block with a `tag` field is added
as the document's first block and comes back when the block is removed. The messages of each version
of the text equal those of an elaboration from scratch.
-/
/--
info: without a tag: [1:26 Missing permalink tag]; as from scratch: true
with a tag: []; as from scratch: true
without a tag again: [1:26 Missing permalink tag]; as from scratch: true
-/
#test_msgs in
run_cmd do
  let title := "#doc (Verso.Genre.Manual) \"Trees\" =>\n\n"
  let untagged := title ++ "Trees grow.\n\nLeaves fall.\n"
  let tagged := title ++ "%%%\ntag := \"trees\"\n%%%\n\nTrees grow.\n\nLeaves fall.\n"
  let mut old? := none
  let mut out := #[]
  for (name, text) in [("without a tag", untagged), ("with a tag", tagged),
      ("without a tag again", untagged)] do
    let edited ← elabInput text old?
    let msgs ← messages edited
    let fromScratch ← messages (← elabInput text none)
    out := out.push s!"{name}: {firstLines msgs}; as from scratch: {msgs == fromScratch}"
    old? := some edited
  logInfo ("\n".intercalate out.toList)

/-
The linter warns on the title of a `#doc` document without blocks.
-/
/-- info: [1:26 Missing permalink tag] -/
#test_msgs in
run_cmd do
  let input := "#doc (Verso.Genre.Manual) \"Trees\" =>\n"
  logInfo s!"{firstLines (← messages (← elabInput input none))}"
