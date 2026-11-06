/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import Verso
import VersoTests.DocCommandInput

/-!
These tests check that an empty `#doc` document (that is, one without blocks) nonetheless results in
a definition. If it didn't, references to the document would fail, and the LSP server wouldn't
return document symbols or folding ranges for it.

After an edit, Lean keeps a command whose syntax is unchanged, with its old elaboration, so whether
the document is empty must be part of the `#doc` command's syntax as a sentinel.
-/

namespace Verso.EmptiedDocumentTest

open Lean Elab Command
open Verso.Doc
open Verso.Tests.DocCommandInput

/--
Elaborates `after` as the remainder of a module, reusing an elaboration of `before`, and logs
whether the document ends up defined.
-/
def checkEdit (before after : String) : CommandElabM Unit := do
  -- Lean's command-line driver sets this option. With it, the snapshots don't keep commands'
  -- syntax, so no command is reused.
  let opts := (← getOptions).setBool `internal.cmdlineSnapshots false
  let run (input : String) (old? : Option IncrementalState) : CommandElabM IncrementalState := do
    IO.processCommandsIncrementally (Parser.mkInputContext input "Input.lean") {}
      (Command.mkState (← getEnv) {} opts) old?
  let edited ← run after (some (← run before none))
  -- The last command is the end of the input, which is elaborated again after any edit, so its
  -- environment is that of the edited text.
  logInfo m!"document defined: {edited.commandState.env.contains (docName (← getMainModule))}"

/-
This test checks that deleting the only block of a document leaves the document defined. The
whitespace after `=>` is the same before and after the edit. In prior versions of the `#doc`
command, its syntax was then unchanged, and Lean kept its old elaboration, which didn't finish the
document.
-/
/-- info: document defined: true -/
#test_msgs in
run_cmd
  checkEdit "#doc (Verso.Doc.Genre.none) \"Trees\" =>\n\nTrees grow in the spring.\n"
    "#doc (Verso.Doc.Genre.none) \"Trees\" =>\n\n"

/-
This test checks that a document whose only content is a Lean comment is defined and empty; the
right result for such a document is undecided. The comment is part of the whitespace after `=>`, so
no block command follows. In prior versions of the `#doc` command, the document was not defined.
-/
/-- info: Verso.Doc.Part.mk #[Verso.Doc.Inline.text "Trees"] "Trees" none #[] #[] -/
#test_msgs in
run_cmd do
  let (env, _) ←
    elabModuleRest "#doc (Verso.Doc.Genre.none) \"Trees\" =>\n\n-- Leaves fall in the autumn.\n"
  let doc ← evalDoc env (← getOptions) (docName (← getMainModule))
  logInfo m!"{repr doc.toPart}"
