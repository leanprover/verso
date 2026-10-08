/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import Verso
import VersoManual
import VersoTests.Refs.AcrossBlocks
import VersoTests.Refs.ManualFootnote
import VersoTests.Refs.SameName

/-!
These tests check link and footnote label resolution in documents that the {lit}`#doc` command
elaborates block by block. They also check that Verso finishes such a document even when its last
block fails.

Each top-level block of a {lit}`#doc` document is its own Lean command, so a label definition and
its uses can be in different commands. Verso finishes the document in the command parsed from the
last block. That's when it checks the links and footnotes and defines the document constant.

The first tests evaluate documents from other modules and observe their values. The later tests
elaborate a document from a string with Lean's command loop. They observe which command reported
each message, and the value of the document.
-/

set_option guard_msgs.diff true

namespace Verso.RefsTest.DocCommand

open Lean Elab Command
open Verso.Doc

/-
Uses resolve across top-level blocks, whether the definition comes before or after the use.

The document in `VersoTests.Refs.AcrossBlocks` has link and footnote uses before and after their
definitions. The uses are in paragraphs, a header, a quote and a list, and some footnote bodies use
earlier links and footnotes. In the value of the document, each use has the URL or contents of its
definition. A use that didn't resolve would have the empty URL or empty contents. The contents of
`[^later]` include a nested footnote, which shows that a footnote body can use the footnotes defined
before it.
-/

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Across blocks"]
  "Across blocks"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "A ",
        Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "forward link")] "https://example.com/later",
        Verso.Doc.Inline.text " and a forward footnote.",
        Verso.Doc.Inline.footnote
          "later"
          #[(Verso.Doc.Inline.text "A later footnote that uses an earlier one."),
            (Verso.Doc.Inline.footnote
               "earlier"
               #[(Verso.Doc.Inline.text "An earlier footnote with a "),
                 (Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "link")] "https://example.com/earlier"),
                 (Verso.Doc.Inline.text ".")])]]]
  #[Verso.Doc.Part.mk
      #[Verso.Doc.Inline.text "A section with an ",
        Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "earlier link")] "https://example.com/earlier"]
      "A section with an  earlier link"
      none
      #[Verso.Doc.Block.blockquote
          #[(Verso.Doc.Block.para
               #[Verso.Doc.Inline.text "A quote with a ",
                 Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "forward link")] "https://example.com/later",
                 Verso.Doc.Inline.text " and a footnote.",
                 Verso.Doc.Inline.footnote
                   "earlier"
                   #[(Verso.Doc.Inline.text "An earlier footnote with a "),
                     (Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "link")] "https://example.com/earlier"),
                     (Verso.Doc.Inline.text ".")]])],
        Verso.Doc.Block.ul
          #[{ contents := #[Verso.Doc.Block.para
                              #[Verso.Doc.Inline.text "A list item with a ",
                                Verso.Doc.Inline.link
                                  #[(Verso.Doc.Inline.text "backward link")]
                                  "https://example.com/earlier",
                                Verso.Doc.Inline.text "."]] }],
        Verso.Doc.Block.para
          #[Verso.Doc.Inline.text "A ",
            Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "backward link")] "https://example.com/later",
            Verso.Doc.Inline.text " after the definitions.",
            Verso.Doc.Inline.footnote
              "later"
              #[(Verso.Doc.Inline.text "A later footnote that uses an earlier one."),
                (Verso.Doc.Inline.footnote
                   "earlier"
                   #[(Verso.Doc.Inline.text "An earlier footnote with a "),
                     (Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "link")] "https://example.com/earlier"),
                     (Verso.Doc.Inline.text ".")])],
            Verso.Doc.Inline.linebreak "\n"]]
      #[]]
-/
#test_msgs in
#eval %doc VersoTests.Refs.AcrossBlocks

/-
Each use resolves to the definition in its own document, even when other documents in the same
module define the same labels.

The module `VersoTests.Refs.SameName` has two `#docs` documents and one `#doc` document. All three
define the same link and footnote labels with different values. The value of each document shows
its own URL and footnote contents.
-/

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Third"]
  "Third"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "A ", Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "link")] "https://example.com/third",
        Verso.Doc.Inline.text ".",
        Verso.Doc.Inline.footnote
          "shared"
          #[(Verso.Doc.Inline.text "The third footnote."), (Verso.Doc.Inline.linebreak "\n")]]]
  #[]
-/
#test_msgs in
#eval %doc VersoTests.Refs.SameName

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "First"]
  "First"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "A ", Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "link")] "https://example.com/first",
        Verso.Doc.Inline.text ".", Verso.Doc.Inline.footnote "shared" #[(Verso.Doc.Inline.text "The first footnote.")]]]
  #[]
-/
#test_msgs in
#eval Verso.RefsTest.SameName.first.toPart

/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Second"]
  "Second"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "A ",
        Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "link")] "https://example.com/second", Verso.Doc.Inline.text ".",
        Verso.Doc.Inline.footnote "shared" #[(Verso.Doc.Inline.text "The second footnote.")]]]
  #[]
-/
#test_msgs in
#eval Verso.RefsTest.SameName.second.toPart

/-
A {lit}`{lean}` role works inside a footnote of a {lit}`Manual` document.

The module `VersoTests.Refs.ManualFootnote` has such a footnote in a {lit}`#docs` document and in
the {lit}`#doc` document. The summary of each footnote's contents shows an inline
{lit}`Verso.Genre.Manual.InlineLean.Inline.lean` whose data mentions {lit}`Nat.succ`. This shows
that the role elaborated and that its highlighted code was restored from the document reconstruction
data. In prior versions of the link and footnote resolution, footnote contents were elaborated with
the {lit}`docReconstructionPlaceholder` unbound, and the role failed with "Unknown identifier
docReconst".
-/

/-- The contents of the first footnote with the label {lit}`label` in {lit}`part`'s own blocks. -/
def footnoteIn (label : String) (part : Part Genre.Manual) : Option (Array (Inline Genre.Manual)) :=
  part.content.findSome? block
where
  block : Block Genre.Manual → Option (Array (Inline Genre.Manual))
    | .para xs => xs.findSome? inline
    | _ => none
  inline : Inline Genre.Manual → Option (Array (Inline Genre.Manual))
    | .footnote l xs => if l == label then some xs else none
    | _ => none

/--
A summary of footnote contents: the text, and for each other inline, its name and whether its data
mentions {lit}`Nat.succ`.
-/
def summarize (xs : Array (Inline Genre.Manual)) : List String :=
  xs.toList.map fun
    | .text s => s!"text {s.quote}"
    | .other i _ => s!"other {i.name} (mentions Nat.succ: {(i.data.compress.find? "Nat.succ").isSome})"
    | .link _ url => s!"link {url.quote}"
    | _ => "other inline"

/--
info: some
  ["text \"A note about \"", "other Verso.Genre.Manual.InlineLean.Inline.lean (mentions Nat.succ: true)", "text \".\""]
-/
#test_msgs in
#eval (footnoteIn "note" Verso.RefsTest.ManualFootnote.allAtOnce.toPart).map summarize

/--
info: some
  ["text \"A note about \"", "other Verso.Genre.Manual.InlineLean.Inline.lean (mentions Nat.succ: true)",
    "text \", with a \"", "link \"https://example.com\"", "text \".\"", "other inline"]
-/
#test_msgs in
#eval (footnoteIn "note" (%doc VersoTests.Refs.ManualFootnote)).map summarize

/-!
The remaining tests elaborate a {lit}`#doc` command from a string with Lean's command loop, so that
documents with errors can be checked. Messages are shown with the number of the command that
reported them. Command 0 is the {lit}`#doc` command itself, and command {lit}`k` is the document's
{lit}`k`-th top-level block.
-/

/-- Renders a message with its position. -/
def showMessage (m : Message) : IO String := do
  let severity := match m.severity with
    | .error => "error"
    | .warning => "warning"
    | .information => "info"
  return s!"{m.pos.line}:{m.pos.column}: {severity}: {← m.data.toString}"

/--
Elaborates {lit}`input` as the rest of a module, in the current environment. Returns the resulting
environment, and each command's messages rendered with the command's number.
-/
def elabModuleRest (input : String) : CommandElabM (Environment × String) := do
  let inputCtx := Parser.mkInputContext input "RefsInput.lean"
  let st ← IO.processCommandsIncrementally inputCtx {}
    (Command.mkState (← getEnv) {} (← getOptions)) none
  let mut out := #[]
  let mut snap := st.initialSnap
  let mut i := 0
  repeat
    let msgs := Language.toSnapshotTree snap.elabSnap |>.getAll
      |>.map (·.diagnostics.msgLog) |>.foldl (· ++ ·) MessageLog.empty
    for m in msgs.toList do
      out := out.push s!"command {i}: {← showMessage m}"
    i := i + 1
    match snap.nextCmdSnap? with
    | some next => snap := next.task.get
    | none => break
  return (st.commandState.env, "\n".intercalate out.toList)

unsafe def evalDocUnsafe (env : Environment) (opts : Options) (n : Name) : IO (VersoDoc Genre.none) :=
  IO.ofExcept <| env.evalConst (VersoDoc Genre.none) opts n

/-- Evaluates the document constant {lit}`n` of {lit}`env`. -/
@[implemented_by evalDocUnsafe]
opaque evalDoc (env : Environment) (opts : Options) (n : Name) : IO (VersoDoc Genre.none)

/--
Elaborates {lit}`input`, which ends with a {lit}`#doc` command, and logs its messages and its
document.
-/
def checkDocInput (input : String) : CommandElabM Unit := do
  let (env, msgs) ← elabModuleRest input
  logInfo msgs
  let docName := Verso.Doc.docName (← getMainModule)
  if env.contains docName then
    match ← (evalDoc env (← getOptions) docName).toBaseIO with
    | .ok doc => logInfo m!"{repr doc.toPart}"
    | .error _ => logInfo m!"The document is defined, and it contains errors, so it can't be evaluated."
  else
    logInfo m!"The document {docName} is not defined."

/-
In a {lit}`#doc` document, every message about links and footnotes appears, and the document is
still defined.
-/

/--
info: command 5: 11:1: error: Duplicate definition of link label [dup]. It is already defined at line 9, column 1, with the URL 'https://example.com/a'. This definition has the URL 'https://example.com/b'.
command 7: 15:2: error: Duplicate definition of footnote label [^dupNote]. It is already defined at line 13, column 2.
command 10: 3:12: error: No definition for link [one]
command 10: 5:2: warning: Unused footnote [^unused]
command 10: 7:17: error: No definition for footnote [^two]
command 10: 19:12: error: No definition for link [three]
---
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Errors"]
  "Errors"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "First ", Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "use")] "",
        Verso.Doc.Inline.text "."],
    Verso.Doc.Block.para #[Verso.Doc.Inline.text "A footnote use.", Verso.Doc.Inline.footnote "two" #[]],
    Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "Uses of ",
        Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "dup")] "https://example.com/a",
        Verso.Doc.Inline.text " and a note.",
        Verso.Doc.Inline.footnote "dupNote" #[(Verso.Doc.Inline.text "The first.")]],
    Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "Third ", Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "use")] "",
        Verso.Doc.Inline.text " and ",
        Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "a defined link")] "https://example.com/defined",
        Verso.Doc.Inline.text "."]]
  #[]
-/
#test_msgs in
#eval checkDocInput "#doc (.none) \"Errors\" =>

First [use][one].

[^unused]: A footnote that nothing uses.

A footnote use.[^two]

[dup]: https://example.com/a

[dup]: https://example.com/b

[^dupNote]: The first.

[^dupNote]: The second.

Uses of [dup][dup] and a note.[^dupNote]

Third [use][three] and [a defined link][defined].

[defined]: https://example.com/defined
"

/-
Verso finishes a {lit}`#doc` document even when its last block fails. This ensures that errors in
the last block don't obliterate info from earlier blocks that should be saved.
-/

/--
info: command 3: 7:1: error: Duplicate definition of link label [d]. It is already defined at line 5, column 1, with the URL 'https://example.com/a'. This definition has the URL 'https://example.com/b'.
command 3: 3:12: error: No definition for link [one]
command 3: 5:1: warning: Unused link [d]
---
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Last block is a duplicate"]
  "Last block is a duplicate"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "First ", Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "use")] "",
        Verso.Doc.Inline.text "."]]
  #[]
-/
#test_msgs in
#eval checkDocInput "#doc (.none) \"Last block is a duplicate\" =>

First [use][one].

[d]: https://example.com/a

[d]: https://example.com/b
"

/--
info: command 2: 5:3: error: No registered directive `nosuch`.
command 2: 3:12: error: No definition for link [one]
---
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Last block is an unknown directive"]
  "Last block is an unknown directive"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "First ", Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "use")] "",
        Verso.Doc.Inline.text "."]]
  #[]
-/
#test_msgs in
#eval checkDocInput "#doc (.none) \"Last block is an unknown directive\" =>

First [use][one].

:::nosuch
Text.
:::
"

/--
info: command 2: 5:0: error: Wrong header nesting - got ### but expected at most #
command 2: 3:12: error: No definition for link [one]
---
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Last block is a header that is too deep"]
  "Last block is a header that is too deep"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "First ", Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "use")] "",
        Verso.Doc.Inline.text "."]]
  #[]
-/
#test_msgs in
#eval checkDocInput "#doc (.none) \"Last block is a header that is too deep\" =>

First [use][one].

### A header that is too deep
"

/-
In a {lit}`#doc` document, an error in a footnote's contents is reported once, in the footnote's own
block.
-/

open Verso.Doc.Elab in
/-- A role that elaborates to an ill-typed inline. -/
@[role]
def illTyped : RoleExpanderOf Unit
  | (), _ => ``(Verso.Doc.Inline.text (5 : Nat))

/--
info: command 2: 5:8: error: Application type mismatch: The argument
  5
has type
  Nat
but is expected to have type
  String
in the application
  Verso.Doc.Inline.text 5
---
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Footnote error"]
  "Footnote error"
  none
  #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "Text.", Verso.Doc.Inline.footnote "f" #[]],
    Verso.Doc.Block.para #[Verso.Doc.Inline.text "A later paragraph.", Verso.Doc.Inline.linebreak "\n"]]
  #[]
-/
#test_msgs in
#eval checkDocInput "#doc (.none) \"Footnote error\" =>

Text.[^f]

[^f]: A {Verso.RefsTest.DocCommand.illTyped}[] body.

A later paragraph.
"

/-
A parse error in the last block doesn't hide the messages about links and footnotes in earlier
blocks.
-/

/--
info: command 3: 3:12: error: No definition for link [one]
---
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Last block has a parse error"]
  "Last block has a parse error"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "First ", Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "use")] "",
        Verso.Doc.Inline.text "."],
    Verso.Doc.Block.para #[Verso.Doc.Inline.text "Second."],
    Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "A ",
        Verso.Doc.Inline.bold #[(Verso.Doc.Inline.text "bold never closed "), (Verso.Doc.Inline.concat #[])]]]
  #[]
-/
#test_msgs in
#eval checkDocInput "#doc (.none) \"Last block has a parse error\" =>

First [use][one].

Second.

A *bold never closed {role
"

/-
An unclosed role at the end of the file doesn't hide these messages either. The role is in a block
with a link use, after a link definition, or after a paragraph.
-/

/--
info: command 2: 3:12: error: No definition for link [one]
---
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Unclosed role with a use"]
  "Unclosed role with a use"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "First ", Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "use")] "",
        Verso.Doc.Inline.text "."],
    Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "Broken ", Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "u")] "",
        Verso.Doc.Inline.text " then ", Verso.Doc.Inline.concat #[]]]
  #[]
-/
#test_msgs in
#eval checkDocInput "#doc (.none) \"Unclosed role with a use\" =>

First [use][one].

Broken [u][two] then {role
"

/--
info: command 3: 3:12: error: No definition for link [one]
command 3: 5:1: warning: Unused link [d]
---
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Unclosed role after a definition"]
  "Unclosed role after a definition"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "First ", Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "use")] "",
        Verso.Doc.Inline.text "."],
    Verso.Doc.Block.para #[Verso.Doc.Inline.text "Broken then ", Verso.Doc.Inline.concat #[]]]
  #[]
-/
#test_msgs in
#eval checkDocInput "#doc (.none) \"Unclosed role after a definition\" =>

First [use][one].

[d]: https://example.com/d

Broken then {role
"

/--
info: command 3: 3:12: error: No definition for link [one]
---
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Unclosed role after a paragraph"]
  "Unclosed role after a paragraph"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "First ", Verso.Doc.Inline.link #[(Verso.Doc.Inline.text "use")] "",
        Verso.Doc.Inline.text "."],
    Verso.Doc.Block.para #[Verso.Doc.Inline.text "Second."],
    Verso.Doc.Block.para #[Verso.Doc.Inline.text "Broken then ", Verso.Doc.Inline.concat #[]]]
  #[]
-/
#test_msgs in
#eval checkDocInput "#doc (.none) \"Unclosed role after a paragraph\" =>

First [use][one].

Second.

Broken then {role
"
