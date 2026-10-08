/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Errata
import Lean.Parser
import Verso.Parser
import Verso.SyntaxUtils

/-!
These tests check that Verso's top-level block commands satisfy an _incremental parsing invariant_
on documents with parse errors. When the invariant is not satisfied, the editor shows stale errors,
folds and symbols.

The incremental parsing invariant says that the parse of a top-level block command doesn't depend on
any text that follows the end of the command after next. Lean's command loop relies on it. After an
edit, Lean reuses a command without parsing it again if the command after next ends before the first
changed byte. Verso parses each top-level block of a `#doc` document as one command. When a block
fails to parse, error recovery makes it a command anyway. For Verso, the takeaway is that a
recovered command must end at or after all the text that its parser read.

Each test splits a document into commands with `blockCommandRecovery`. This is the parser that
`versoBlockCommandFn` uses for each top-level block, with Verso's error recovery. Then the test
checks each command that has a command after next. At each line start after the end of the command
after next, it changes the text in each of the ways listed in `changes`. It parses the command again
from its start. The syntax, the end position and the errors must match the first parse.

The documents are small. Each has a parse error in one block, followed by more paragraphs. In most
of them, the error is the unfinished role `{hig`. The interactive test
`parse_errors_blockquote_in_directive.lean` checks one of these documents through the language
server.
-/

namespace Verso.IncrementalParsingTest

open Lean Parser Verso.Parser Errata

/-- The result of parsing one command: its syntax, its end position and its errors. -/
structure Parsed where
  stx : String
  endPos : String.Pos.Raw
  errors : List (String.Pos.Raw × String)
  failed : Bool
deriving BEq, Repr

/-- Parses the command that starts at position `pos` of `input`. -/
def parseAt (input : String) (pos : String.Pos.Raw) : IO Parsed := do
  let env ← mkEmptyEnvironment
  let ictx := mkInputContext input "<input>"
  let pmctx : ParserModuleContext := { env, options := {} }
  let s :=
    blockCommandRecovery.run ictx pmctx (getTokenTable env) ((mkParserState input).setPos pos)
  let stx := if s.stxStack.size > 0 then toString s.stxStack.back else ""
  let errors := s.allErrors.toList.map fun (p, _, e) => (p, toString e)
  return { stx, endPos := s.pos, errors, failed := s.hasError }

/-- Splits a document into top-level block commands, returning each start position and result. -/
def commands (input : String) : IO (Array (String.Pos.Raw × Parsed)) := do
  let env ← mkEmptyEnvironment
  let ictx := mkInputContext input "<input>"
  let pmctx : ParserModuleContext := { env, options := {} }
  let s := (ignoreFn (manyFn blankLine)).run ictx pmctx (getTokenTable env) (mkParserState input)
  let mut pos := s.pos
  let mut out := #[]
  while pos < input.rawEndPos do
    let r ← parseAt input pos
    out := out.push (pos, r)
    if r.failed || r.endPos ≤ pos then break
    pos := r.endPos
  return out

/--
The ways the text is changed after a cut point: it is cut off there, or text is added at the cut
point. The additions close or open inline markup and blocks, change indentation, and add lines.
-/
def changes (input : String) (cut : String.Pos.Raw) : List String :=
  let pre := String.Pos.Raw.extract input 0 cut
  let rest := String.Pos.Raw.extract input cut input.rawEndPos
  [pre, pre ++ "]\n", pre ++ "[x]\n", pre ++ "}\n", pre ++ "x\n\ny\n", pre ++ "> q\n",
   pre ++ "[" ++ rest, pre ++ "]" ++ rest, pre ++ "}" ++ rest, pre ++ "{" ++ rest,
   pre ++ ":::\n" ++ rest, pre ++ "*" ++ rest, pre ++ "```\n" ++ rest, pre ++ "  " ++ rest,
   pre ++ "\n" ++ rest, pre ++ "x" ++ rest]

/-- The positions where lines of `input` start. -/
def lineStarts (input : String) : Array String.Pos.Raw :=
  let (_, out) := input.foldl (init := ((0 : String.Pos.Raw), #[(0 : String.Pos.Raw)]))
    fun (pos, out) c =>
      let pos := pos + c
      (pos, if c == '\n' then out.push pos else out)
  out

/--
Finds the commands whose parse changes when text after the end of the command after next changes.
Each result describes the command, the cut point and the changed text.
-/
def violations (input : String) : IO (Array String) := do
  let cmds ← commands input
  let mut out := #[]
  for h : j in [0:cmds.size] do
    let some (_, after) := cmds[j + 2]? | continue
    let (start, parsed) := cmds[j]
    let mut found := false
    for cut in lineStarts input do
      if found then break
      if cut < after.endPos then continue
      for changed in changes input cut do
        let parsed' ← parseAt changed start
        if parsed' != parsed then
          let suffix := String.Pos.Raw.extract changed cut changed.rawEndPos
          out := out.push s!"command {j} at byte {start.byteIdx} ends at {parsed.endPos.byteIdx}, \
            and the command after next ends at {after.endPos.byteIdx}. Changing the text at byte \
            {cut.byteIdx} to {repr suffix} changes its parse to end at {parsed'.endPos.byteIdx} \
            with errors at {parsed'.errors.map (·.1.byteIdx)}, where it had errors at \
            {parsed.errors.map (·.1.byteIdx)}."
          found := true
          break
  return out

/-- Asserts that `input` satisfies the incremental parsing invariant. -/
def checkInvariant (input : String) : Test := do
  let cmds ← commands input
  assertTrue (cmds.size ≥ 3) "the document splits into at least three commands"
    (detail? := some s!"{cmds.size} commands")
  let found ← violations input
  assertTrue found.isEmpty "a command's parse depends on text after the command after next"
    (detail? := some ("\n".intercalate found.toList))

/--
A blockquote whose fourth paragraph is the unfinished role `{hig`. This is the basic case. In prior
versions of the blockquote parser, this document broke the invariant. The blockquote failed at its
`>`, so its recovered command ended after its first paragraph. Its parser had read up to the error,
which is after the command after next.
-/
def blockquote3 : String :=
"> The weather was nice today.

  We went for a walk.

  The park was quiet.

  {hig

Then we went home.

We had dinner.

We went to bed.

We slept well.

The next day was sunny.
"

@[test] def blockquoteThreeParagraphs : Test := checkInvariant blockquote3

/--
A blockquote with five paragraphs before the unfinished role. In prior versions of the blockquote
parser, this document broke the invariant.
-/
def blockquote5 : String :=
"> The weather was nice today.

  We went for a walk.

  The park was quiet.

  We sat on a bench.

  Then we went home.

  {hig

We had dinner.

We went to bed.

We slept well.

The next day was sunny.

We went to the beach.
"

@[test] def blockquoteFiveParagraphs : Test := checkInvariant blockquote5

/--
A `:::note` directive whose first block is a blockquote with the unfinished role. In prior versions
of the blockquote parser, this document broke the invariant. Both the directive's command and the
command after it ended before the error.
-/
def blockquoteInDirective : String :=
":::note
> The weather was nice today.

  We went for a walk.

  The park was quiet.

  {hig
:::

Then we went home.

We had dinner.

We went to bed.

We slept well.

The next day was sunny.
"

@[test] def blockquoteInsideDirective : Test := checkInvariant blockquoteInDirective

/--
A blockquote that contains a code block whose closing fence is too short. The code block recovers
from its error, so the blockquote succeeds. This document satisfied the invariant in prior versions
of the blockquote parser too.
-/
def codeInBlockquote : String :=
"> The weather was nice today.

  We went for a walk.

  The park was quiet.

  ```
  Thanks
  ``

Then we went home.

We had dinner.

We went to bed.

We slept well.

The next day was sunny.
"

@[test] def codeBlockInsideBlockquote : Test := checkInvariant codeInBlockquote

/--
A list item that contains a blockquote with the unfinished role. In prior versions of the
blockquote parser, this document broke the invariant. The list item ended at the blockquote.
-/
def blockquoteInList : String :=
"* The weather was nice today.

  > We went for a walk.

    The park was quiet.

    We sat on a bench.

    {hig

Then we went home.

We had dinner.

We went to bed.

We slept well.

The next day was sunny.
"

@[test] def blockquoteInsideListItem : Test := checkInvariant blockquoteInList

/--
A blockquote that contains a list whose item is the unfinished role. In prior versions of the
blockquote parser, this document broke the invariant. The blockquote failed at its `>`, before the
list.
-/
def listInBlockquote : String :=
"> The weather was nice today.

  We went for a walk.

  The park was quiet.

  * {hig

Then we went home.

We had dinner.

We went to bed.

We slept well.

The next day was sunny.
"

@[test] def listInsideBlockquote : Test := checkInvariant listInBlockquote

/--
A list item whose fourth paragraph is the unfinished role, with no blockquote. This document
satisfied the invariant in prior versions of the blockquote parser too, because a list fails at its
error.
-/
def listItem : String :=
"* The weather was nice today.

  We went for a walk.

  The park was quiet.

  {hig

Then we went home.

We had dinner.

We went to bed.

We slept well.

The next day was sunny.
"

@[test] def listItemWithError : Test := checkInvariant listItem

/--
A `:::note` directive whose fourth paragraph is the unfinished role, with no blockquote. This
document satisfied the invariant in prior versions of the blockquote parser too, because a directive
fails at its error.
-/
def directive : String :=
":::note
The weather was nice today.

We went for a walk.

The park was quiet.

{hig
:::

Then we went home.

We had dinner.

We went to bed.

We slept well.

The next day was sunny.
"

@[test] def directiveWithError : Test := checkInvariant directive

/--
Three paragraphs and then a code block whose closing fence is too short. The code block recovers
from its error. This document satisfied the invariant in prior versions of the blockquote parser
too. The code block runs to the end of the text, so only the three paragraphs before it have a
command after next, and only they are checked.
-/
def codeBlock : String :=
"The weather was nice today.

We went for a walk.

The park was quiet.

```
Thanks
``

Then we went home.
"

@[test] def codeBlockWithBrokenFence : Test := checkInvariant codeBlock
