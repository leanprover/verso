import Verso

/-!
This test checks, through the language server, that an edit to a top-level block of a `#doc`
document compiles the blocks from the edited block on, and reuses the compiled definitions of the
blocks before it.

The document has four paragraphs. Each paragraph has the role `{mark}[]`, whose term logs a message
when the block's definition is elaborated. The message quotes the line that starts with "We met on"
as the file reads at that moment. That line begins the third paragraph. The edit changes its
"Tuesday" to "Thursday". The runner prints the diagnostics before and after the edit.

Before the edit, every message quotes "Tuesday". After the edit, the messages of the first two
paragraphs still quote "Tuesday", and those of the last two quote "Thursday". A message keeps its
old text only when Lean reused the command of its block, so the first two blocks were not compiled
again. The new text in the last two messages shows that their blocks were compiled again, each in
its own command.

In prior versions of Verso, every block was compiled in the last block's command. After the edit,
all four messages quoted "Thursday".
-/

open Lean Elab Term Verso Doc Elab

/--
Logs the line of the file that starts with the words "We met on", and elaborates to an empty
inline.
-/
elab "compiledMark%" : term <= expectedType => do
  let line := (← getFileMap).source.lines.find? (·.startsWith "We met on ") |>.map toString
  logInfo m!"Compiled while the file says: {line.getD "nothing"}"
  elabTerm (← ``(Verso.Doc.Inline.concat #[])) expectedType

/-- Marks a block, so that compiling the block logs a message. -/
@[role]
def mark : RoleExpanderOf Unit
  | (), _ => ``(compiledMark%)

#doc (.none) "Meetings" =>

The first meeting {mark}[] was short.

The second meeting {mark}[] was long.
--^ collectDiagnostics

We met on Tuesday.
        --^ change: "Tuesday" "Thursday"
The third meeting {mark}[] was on that day.
--^ collectDiagnostics

The last meeting {mark}[] was in the evening.
