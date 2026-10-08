import Verso

/-!
This test checks, through the language server, that the part of a block before a parse error keeps
its hovers, highlights and definitions. It matters when you change a block parser, its error
recovery or an elaborator. The editor offers these features while a block is being typed.

The document defines the link label `park`. Two paragraphs use it and the role `hig`. The first
paragraph is valid. The second paragraph is the same up to its end, where an unfinished role makes a
parse error. In each paragraph, the runner asks for the hover and the highlights of the label, and
for the hover and the definition of the role name.

The hovers and the definition are the same in both paragraphs. The hover of the label explains link
references. The hover of the role name is the role's documentation, and its definition is the role's
declaration in this file. The highlights of the label are its definition and its uses up to and
including the paragraph.

In prior versions of the error recovery, the second paragraph had no hovers, highlights or
definitions.
-/

open Lean Verso Doc Elab

/-- A genre with no extensions of its own. -/
def TestGenre : Genre where
  PartMetadata := Unit
  Block := Empty
  Inline := Empty
  TraverseContext := Unit
  TraverseState := Unit

/-- Emphasizes its contents. -/
@[role]
def hig : RoleExpanderOf Unit
  | (), contents => do
    let contents ← contents.mapM elabInline
    ``(Verso.Doc.Inline.emph #[$contents,*])

#doc (TestGenre) "Notes" =>

[park]: https://example.com/park

We walked to [the park][park] and saw {hig}[a heron] by {hig}[the lake].
                        --^ textDocument/hover
                        --^ textDocument/documentHighlight
                                       --^ textDocument/hover
                                       --^ textDocument/definition

We walked to [the park][park] and saw {hig}[a heron] by {hig
                        --^ textDocument/hover
                        --^ textDocument/documentHighlight
                                       --^ textDocument/hover
                                       --^ textDocument/definition
