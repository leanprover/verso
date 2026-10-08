/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso

/-!
These tests check the document that a `#doc` command defines when one of its blocks has a parse
error. They matter when you change error recovery or an elaborator. The editor shows this document's
structure while a block is being typed. Verso builds the document from the same elaboration.

The part of a block before its parse error is elaborated as in a valid block. An inline or a block
that the parse error cut short is elaborated with the parts it has. If that elaboration fails, it is
`Inline.empty` or `Block.empty`. A header with a parse error starts a part at its level, with the
part of its title before the error. A metadata block or an include has no effect while it has a
parse error.

Each test elaborates a short document with `#elab_doc`. It prints the messages of the elaboration,
then whether the document is defined and whether it depends on `sorryAx`, then the document.

In prior versions of the error recovery, a block with a parse error was `sorry` in the document. The
document then depended on `sorryAx`.
-/

namespace Verso.PartialSyntaxDocsTest

open Lean Elab Command
open Verso Doc Elab

/-- The metadata of the test genre's parts. -/
structure Meta where
  a : Nat := 0
  b : Nat := 0
deriving Repr

/-- A genre whose parts have metadata and which has no extensions of its own. -/
def TestGenre : Genre := ⟨Meta, Empty, Empty, Unit, Unit⟩

instance : Repr TestGenre.PartMetadata := inferInstanceAs (Repr Meta)
instance : Repr TestGenre.Block := ⟨fun e _ => nomatch (e : Empty)⟩
instance : Repr TestGenre.Inline := ⟨fun e _ => nomatch (e : Empty)⟩

/-- Emphasizes its contents. -/
@[role]
def hig : RoleExpanderOf Unit
  | (), contents => do
    let contents ← contents.mapM elabInline
    ``(Verso.Doc.Inline.emph #[$contents,*])

/-- Evaluates the document named `name` in `env`. -/
unsafe def evalDocUnsafe (env : Environment) (opts : Options) (name : Name) :
    Except String (Part TestGenre) :=
  (env.evalConst (VersoDoc TestGenre) opts name).map VersoDoc.toPart

@[implemented_by evalDocUnsafe]
opaque evalDoc (env : Environment) (opts : Options) (name : Name) : Except String (Part TestGenre)

/--
Elaborates the given string as the body of a `#doc (TestGenre) "Notes" =>` command, as a separate
file in the current environment. Logs the messages, whether the document is defined and whether it
depends on `sorryAx`. When the document is free of `sorryAx`, also logs the document.
-/
elab "#elab_doc " body:str : command => do
  let input := "open Verso.PartialSyntaxDocsTest\n#doc (TestGenre) \"Notes\" =>\n\n" ++ body.getString
  let inputCtx := Parser.mkInputContext input "<doc>"
  let commandState : Command.State := { env := (← getEnv), maxRecDepth := (← get).maxRecDepth }
  let s ← IO.processCommands inputCtx {} commandState
  let mut out := #[]
  for m in s.commandState.messages.toList do
    out := out.push s!"{m.pos.line}:{m.pos.column}: {(← m.data.toString).trimAscii}"
  let env := s.commandState.env
  let name := docName (← getMainModule)
  if env.contains name then
    let axioms ← withEnv env <| liftCoreM <| collectAxioms name
    out := out.push s!"defined, depends on sorryAx: {axioms.contains ``sorryAx}"
    unless axioms.contains ``sorryAx do
      match evalDoc env (← getOptions) name with
      | .ok part => out := out.push s!"{repr part}"
      | .error e => out := out.push s!"evaluation failed: {e}"
  else
    out := out.push "not defined"
  logInfo ("\n".intercalate out.toList)

/-! # Partial blocks -/

/-
This test checks that the part of a paragraph before an unfinished role is in the document.
-/
/--
info: 6:53: unexpected newline; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
defined, depends on sorryAx: false
Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Notes"]
  "Notes"
  none
  #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "We went to the park."],
    Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "We walked to the lake and saw ",
        Verso.Doc.Inline.emph #[(Verso.Doc.Inline.text "a heron")], Verso.Doc.Inline.text " and ",
        Verso.Doc.Inline.emph #[], Verso.Doc.Inline.linebreak "\n"]]
  #[]
-/
#guard_msgs in
#elab_doc "We went to the park.

We walked to the lake and saw {hig}[a heron] and {hig
"

/-
This test checks that a list item before a parse error is in the document. The second item is cut
short at the unfinished role.
-/
/--
info: 6:15: unexpected newline; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
defined, depends on sorryAx: false
Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Notes"]
  "Notes"
  none
  #[Verso.Doc.Block.ul
      #[{ contents := #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "We saw a heron."]] },
        { contents := #[Verso.Doc.Block.para
                          #[Verso.Doc.Inline.text "We saw a ", Verso.Doc.Inline.emph #[],
                            Verso.Doc.Inline.linebreak "\n"]] }]]
  #[]
-/
#guard_msgs in
#elab_doc "* We saw a heron.

* We saw a {hig
"

/-
This test checks that a footnote definition with a parse error still defines the footnote. The
footnote in the paragraph has the contents before the error.
-/
/--
info: 6:43: unexpected newline; expected positional argument, named argument, flag, or '}' (use '\{' for a literal '{')
defined, depends on sorryAx: false
Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Notes"]
  "Notes"
  none
  #[Verso.Doc.Block.para
      #[Verso.Doc.Inline.text "We went to the park.",
        Verso.Doc.Inline.footnote
          "walk"
          #[(Verso.Doc.Inline.text "We walked to the lake and saw "),
            (Verso.Doc.Inline.emph #[]),
            (Verso.Doc.Inline.linebreak "\n")]]]
  #[]
-/
#guard_msgs in
#elab_doc "We went to the park.[^walk]

[^walk]: We walked to the lake and saw {hig
"

/-! # Blocks that change the document's structure -/

/-
This test checks that a header with a parse error starts a part. The title is the text before the
error. It is `Head` and then `Inline.empty`, which is the unclosed bold text. The paragraph after
the header is in the part.
-/
/--
info: 6:12: unexpected newline; expected '*' to close bold text
defined, depends on sorryAx: false
Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Notes"]
  "Notes"
  none
  #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "Before."]]
  #[Verso.Doc.Part.mk
      #[Verso.Doc.Inline.text "Head ", Verso.Doc.Inline.concat #[]]
      "Head "
      none
      #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "After.", Verso.Doc.Inline.linebreak "\n"]]
      #[]]
-/
#guard_msgs in
#elab_doc "Before.

# Head *bold

After.
"

/-
This test checks that a metadata block with a parse error sets no metadata. The document has no
error other than the parse error.
-/
/--
info: 9:0: expected field index or identifier
defined, depends on sorryAx: false
Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Notes"]
  "Notes"
  none
  #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "After.", Verso.Doc.Inline.linebreak "\n"]]
  #[]
-/
#guard_msgs in
#elab_doc "%%%
a := 1
b.
%%%

After.
"

/-
This test checks that a second metadata block sets the metadata when the first one has a parse
error. In prior versions of the error recovery, the first block was content. The second block then
had the error `Metadata blocks must precede both content and subsections`.
-/
/--
info: 6:6: unexpected token '%%%'; expected ')', '_', identifier or term
defined, depends on sorryAx: false
Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Notes"]
  "Notes"
  (some { a := 0, b := 2 })
  #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "After.", Verso.Doc.Inline.linebreak "\n"]]
  #[]
-/
#guard_msgs in
#elab_doc "%%%
a := 1
b := (
%%%

%%%
b := 2
%%%

After.
"

/-
This test checks that an unclosed metadata block at the end of the document sets no metadata. The
document is still defined.
-/
/--
info: 8:0: expected %%% (at line beginning)
defined, depends on sorryAx: false
Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Notes"]
  "Notes"
  none
  #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "Before."]]
  #[]
-/
#guard_msgs in
#elab_doc "Before.

%%%
a := 1
"

end Verso.PartialSyntaxDocsTest
