/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import Verso

/-!
These tests check the document that a `#doc` command defines when one of its blocks has a parse
error. They matter when you change error recovery or an elaborator. The editor shows this document's
structure while a block is being typed. Verso builds the document from the same elaboration.

The part of a block before its parse error is elaborated as in a valid block. An inline or a block
that the parse error cut short is elaborated with the parts it has. If that elaboration fails, it is
`Inline.empty` or `Block.empty`. A header with a parse error starts a part at its level, with the
part of its title before the error. A metadata block or an include has no effect while it has a
parse error. When a block's parser fails after it has read whole blocks, error recovery gives a null
node whose children are these blocks and `Syntax.missing`. Each of these blocks is elaborated in
order as a block with a parse error. In a block with a parse error, a node that no elaborator
accepts results in `Inline.empty` or `Block.empty`.

Most tests elaborate a short document with `#elab_doc`. It prints the messages of the elaboration,
then whether the document is defined and whether it depends on `sorryAx`, then the document. No
parser gives some of the null nodes under test. For these, `elabNullDoc` builds the syntax of a
`#docs` command with its first blocks in a null node, and prints the first line of each message and
the document.

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
Formats each message as its line, column and text. With `firstLines`, only the first line of each
message's text is kept.
-/
def formatMessages (messages : MessageLog) (firstLines : Bool := false) : IO (Array String) := do
  let mut out := #[]
  for m in messages.toList do
    let text := (← m.data.toString).trimAscii
    let text := if firstLines then text.takeWhile (· != '\n') else text
    out := out.push s!"{m.pos.line}:{m.pos.column}: {text}"
  return out

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
  let mut out ← formatMessages s.commandState.messages
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

/--
Elaborates the given string as the body of a `#docs (TestGenre) nullDoc "Notes"` command. The first
`count` top-level blocks, each transformed by `edit`, and then `Syntax.missing` are put in one null
node. `recoverPartialBlock` gives syntax of this shape when a top-level block's parser leaves these
trees. Logs the first line of each message of the elaboration, then the document.
-/
def elabNullDoc (body : String) (count : Nat) (edit : Syntax → Syntax := id) : CommandElabM Unit := do
  let input := "#docs (TestGenre) nullDoc \"Notes\" :=\n:::::::\n" ++ body ++ ":::::::\n"
  let stx ← match Parser.runParserCategory (← getEnv) `command input "<doc>" with
    | .ok stx => pure stx
    | .error e => throwError e
  let some i := stx.getArgs.findIdx? (·.isOfKind nullKind)
    | throwError "The command has no document body: {stx}"
  let blocks := stx[i].getArgs
  let recovered := mkNullNode ((blocks.take count).map edit |>.push .missing)
  let stx := stx.setArg i (mkNullNode (#[recovered] ++ blocks.drop count))
  let priorMessages := (← get).messages
  modify ({ · with messages := {} })
  let (messages, doc) ←
    withReader ({ · with fileMap := .ofString input, fileName := "<doc>" }) <|
    withScope (fun sc => { sc with opts := sc.opts.setBool `pp.rawOnError true }) <|
    withoutModifyingEnv do
      elabCommand stx
      pure ((← get).messages, evalDoc (← getEnv) (← getOptions) ((← getCurrNamespace) ++ `nullDoc))
  modify ({ · with messages := priorMessages })
  let mut out ← formatMessages messages (firstLines := true)
  match doc with
  | .ok part => out := out.push s!"{repr part}"
  | .error e => out := out.push s!"evaluation failed: {e}"
  logInfo ("\n".intercalate out.toList)

/--
Replaces each unordered list by its first list item. A list item outside a list is a fragment of a
block, which no elaborator accepts.
-/
def firstItems (stx : Syntax) : Syntax :=
  stx.rewriteBottomUp fun
    | list@(.node _ ``Lean.Doc.Parser.Block.ul _) =>
      (list.find? (·.isOfKind ``Lean.Doc.Parser.ListItem.item)).getD list
    | other => other

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
#test_msgs in
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
#test_msgs in
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
#test_msgs in
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
#test_msgs in
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
#test_msgs in
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
#test_msgs in
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
#test_msgs in
#elab_doc "Before.

%%%
a := 1
"

/-! # Blocks whose parser fails after their end -/

/-
This test checks that a header whose parser fails after it has read the header opens its part. The
document has the part `Head`, and the paragraph after the header is in that part. The part's title
is `Head ` followed by `Inline.empty`. The role `{hig}` has its name and arguments and no content,
so the parser fails at the end of the line. Error recovery gives a null node whose children are the
header and `Syntax.missing`. In prior versions of Verso, the null node was an empty block,
`Block.concat #[]`, and the document had no part `Head`.
-/
/--
info: 8:0: unexpected newline; expected '![', '$$', '$', '*', '[', '[^', '_', '`' or '{'
defined, depends on sorryAx: false
Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Notes"]
  "Notes"
  none
  #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "We went to the park."]]
  #[Verso.Doc.Part.mk
      #[Verso.Doc.Inline.text "Head ", Verso.Doc.Inline.concat #[]]
      "Head "
      none
      #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "We saw a heron.", Verso.Doc.Inline.linebreak "\n"]]
      #[]]
-/
#test_msgs in
#elab_doc "We went to the park.

# Head {hig}

We saw a heron.
"

/-
This test checks that a paragraph whose parser fails after it has read the paragraph is in the
document. The document has the paragraph with the text `We saw ` followed by `Inline.empty`. The
role `{hig}` has its name and arguments and no content, so error recovery gives a null node whose
children are the paragraph and `Syntax.missing`. In prior versions of Verso, the null node was an
empty block, `Block.concat #[]`, and the paragraph was not in the document.
-/
/--
info: 8:0: unexpected newline; expected '![', '$$', '$', '*', '[', '[^', '_', '`' or '{'
defined, depends on sorryAx: false
Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Notes"]
  "Notes"
  none
  #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "We went to the park."],
    Verso.Doc.Block.para #[Verso.Doc.Inline.text "We saw ", Verso.Doc.Inline.concat #[]],
    Verso.Doc.Block.para #[Verso.Doc.Inline.text "We saw a heron.", Verso.Doc.Inline.linebreak "\n"]]
  #[]
-/
#test_msgs in
#elab_doc "We went to the park.

We saw {hig}

We saw a heron.
"

/-
This test checks that a metadata block whose parser fails after the closing `%%%` is elaborated as
a metadata block with a parse error. The document has no metadata, and its only block is the
paragraph after the metadata block. The text after the closing `%%%` gives the parse error, so error
recovery gives a null node whose children are the whole metadata block and `Syntax.missing`. In
prior versions of Verso, the null node was an empty block, `Block.concat #[]`, before the paragraph.
-/
/--
info: 8:0: '
'; expected expected end of file
defined, depends on sorryAx: false
Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Notes"]
  "Notes"
  none
  #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "After.", Verso.Doc.Inline.linebreak "\n"]]
  #[]
-/
#test_msgs in
#elab_doc "%%%
b := 2
%%% b

After.
"

/-
This test checks that the blocks in a null node are elaborated in order. The paragraph `Before.` is
in the root part, and the header opens the part `Head`. The part `Head` contains the paragraph after
the null node. The null node's children are a paragraph, a header and `Syntax.missing`.
`recoverPartialBlock` gives syntax of this shape when a top-level block's parser leaves several
trees. No parser gives this syntax, so the test builds it. In prior versions of Verso, the null node
was one empty block, `Block.concat #[]`, and the document had no part `Head`.
-/
/--
info: Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Notes"]
  "Notes"
  none
  #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "Before."]]
  #[Verso.Doc.Part.mk
      #[Verso.Doc.Inline.text "Head"]
      "Head"
      none
      #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "After."]]
      #[]]
-/
#test_msgs in
run_cmd elabNullDoc (count := 2) "Before.

# Head

After.
"

/-
This test checks that, in a block that is partial syntax, a node that no elaborator accepts results
in an empty block and the rest of the block is in the document. The document has the blockquote with
`Block.concat #[]` in place of the list item, followed by the paragraph in the blockquote. The
message `unexpected syntax` is logged for the list item. The null node's children are a blockquote
and `Syntax.missing`. In the blockquote, a list item outside a list stands in place of the list,
and no elaborator accepts it. `recoverPartialBlock` gives syntax of this shape when a top-level
block's parser leaves one tree without `Syntax.missing`. No parser gives a list item outside a list,
so the test builds this syntax. In prior versions of Verso, the null node was one empty block, and
the paragraph in the blockquote was not in the document.
-/
/--
info: 3:2: unexpected syntax
Verso.Doc.Part.mk
  #[Verso.Doc.Inline.text "Notes"]
  "Notes"
  none
  #[Verso.Doc.Block.blockquote
      #[(Verso.Doc.Block.concat #[]), (Verso.Doc.Block.para #[Verso.Doc.Inline.text "We saw an egret."])],
    Verso.Doc.Block.para #[Verso.Doc.Inline.text "After."]]
  #[]
-/
#test_msgs in
run_cmd elabNullDoc (count := 1) (edit := firstItems) "> * We saw a heron.

  We saw an egret.

After.
"

end Verso.PartialSyntaxDocsTest
