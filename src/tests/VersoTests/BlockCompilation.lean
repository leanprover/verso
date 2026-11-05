/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import Verso
import VersoTests.DocCommandInput

/-!
These tests check the definitions that Verso creates for the blocks of a document.

Top-level blocks that add content to a document get definitions of their own, which are functions
from the document's reconstruction data to the blocks. Each definition is compiled right after its
block is elaborated, so in {lit}`#doc` documents, errors in block definitions appear with their
blocks. The language server reuses the elaboration of the top-level blocks before an edit, which
works only if the names of block definitions don't depend on whether earlier blocks failed. Several
documents, including several documents elaborated as terms in one declaration, must also coexist in
one module without their definitions colliding.

The tests compare names by relation: whether they are under a document's constant name (which is a
prefix of them), whether they are distinct, and whether a failure changes them. Some of them
elaborate a {lit}`#doc` command from a string with Lean's command loop, so that they can observe the
environment and the messages of each command.

In prior versions of Verso, every block was compiled in the command of a {lit}`#doc` document's last
block, and auxiliary definitions made while a block elaborated had names based on the module's
document name.
-/

set_option guard_msgs.diff true

namespace Verso.Tests.BlockCompilation

open Lean Elab Command
open Verso.Doc Verso.Doc.Elab
open scoped Verso.Doc.Concrete
open Verso.Tests.DocCommandInput

/-- The names of the constants of {name}`env` that are under {name}`pre`, other than {name}`pre`. -/
def constantsUnder (pre : Name) (env : Environment) : Array Name := Id.run do
  let mut acc := #[]
  for (n, _) in env.constants.map₂ do
    if pre.isPrefixOf n && n != pre then acc := acc.push n
  return acc

/-- The type of the block definitions of a document in the genre {name}`Genre.none`. -/
def blockDefinitionType : MetaM Expr :=
  mkArrow (mkApp (mkConst ``DocReconstruction) (mkConst ``Genre.none))
    (mkApp (mkConst ``Verso.Doc.Block) (mkConst ``Genre.none))

/-- Whether the constant {name}`n` has the type {name}`type`. -/
def hasType (type : Expr) (n : Name) : MetaM Bool := do
  Meta.isDefEq (← getConstInfo n).type type

/-- The texts of the inlines of the document's paragraphs, by paragraph. -/
def paragraphTexts (doc : VersoDoc Genre.none) : Array (Array String) :=
  doc.toPart.content.filterMap fun
    | .para inlines => some <| inlines.filterMap fun
      | .text s => some s
      | _ => none
    | _ => none

def twoTermDocuments : VersoDoc .none × VersoDoc .none := (
  verso (.none) "A Document Term"
  :::
  A paragraph in a document term.
  :::,
  verso (.none) "Another Document Term"
  :::
  A paragraph in another document term.
  :::)

/-
Documents elaborated as terms in one declaration each evaluate to their own content and have a
constant of their own, and each block definition is under exactly one of these constants.
-/

/--
info: Each document has its own paragraph: true
Documents: 2
Block definitions: 2
Each block definition is under a different document: true
-/
#test_msgs in
#eval show MetaM Unit from do
  let ownContent :=
    paragraphTexts twoTermDocuments.1 == #[#["A paragraph in a document term."]] &&
    paragraphTexts twoTermDocuments.2 == #[#["A paragraph in another document term."]]
  let under := constantsUnder ``twoTermDocuments (← getEnv)
  let docType := mkApp (mkConst ``VersoDoc) (mkConst ``Genre.none)
  let docs ← under.filterM (hasType docType)
  let blocks ← under.filterM (hasType (← blockDefinitionType))
  let owners := blocks.map fun b => docs.filter (·.isPrefixOf b)
  let separate := owners.all (·.size == 1) && (owners.map (·[0]?)).toList.eraseDups.length == 2
  logInfo m!"Each document has its own paragraph: {ownContent}\n\
    Documents: {docs.size}\nBlock definitions: {blocks.size}\n\
    Each block definition is under a different document: {separate}"

/-- A role that elaborates to the text of the local variable {lit}`x`. -/
@[role]
def localX : RoleExpanderOf Unit
  | (), _ => ``(Verso.Doc.Inline.text (toString $(mkIdent `x)))

/-
A block of a document term that refers to a local variable of the enclosing declaration gets one
error, which mentions the variable.
-/

/--
error: Can't refer to a local variable here (reference to `x`).
-/
#test_msgs in
set_option linter.unusedVariables false in
def blockMentionsX (x : Nat) : VersoDoc .none := verso (.none) "A block mentions x"
  :::
  The value is {localX}[].
  :::

/-
A document term whose title refers to a local variable of the enclosing declaration gets one error,
which mentions the variable.
-/

/--
error: Can't refer to a local variable here (reference to `x`).
-/
#test_msgs in
set_option linter.unusedVariables false in
def titleMentionsX (x : Nat) : VersoDoc .none := verso (.none) "The title mentions {localX}[]"
  :::
  A paragraph.
  :::

/-- A role that elaborates to an ill-typed inline. Only compiling the block finds the error. -/
@[role]
def illTyped : RoleExpanderOf Unit
  | (), _ => ``(Verso.Doc.Inline.text (5 : Nat))

/-- A document whose second paragraph has a role that elaborates to an ill-typed inline. -/
def compileErrorInput : String := "#doc (.none) \"Compile error\" =>

A first paragraph.

A paragraph with {Verso.Tests.BlockCompilation.illTyped}[] in it.

A last paragraph.
"

/-
An error that is found only when a block is compiled is reported in the block's own command, here
command 2 for the second paragraph, and the document is still defined.
-/

/--
info: command 2: 5:17
---
info: The document is defined: true
-/
#test_msgs in
#eval do
  let (env, msgs) ← elabModuleRest compileErrorInput
  let lines := (msgs.splitOn "\n").filter fun (line : String) => line.startsWith "command "
  let positions := lines.map fun (line : String) => ": ".intercalate ((line.splitOn ": ").take 2)
  logInfo ("\n".intercalate positions)
  logInfo m!"The document is defined: {env.contains (docName (← getMainModule))}"

/-- A directive whose expander throws an error. -/
@[directive]
def failing : DirectiveExpanderOf Unit
  | (), _ => throwError "The directive fails."

/-- A directive that elaborates to an empty paragraph. -/
@[directive]
def succeeding : DirectiveExpanderOf Unit
  | (), _ => ``(Verso.Doc.Block.para #[])

open PartElabM in
/-- A part command for the directive {lit}`twoBlocks`, which adds two paragraphs to the document. -/
@[part_command Lean.Doc.Parser.Block.directive]
def twoBlocks : PartCommand
  | .directive v => do
    unless v.name.getId == `twoBlocks do throwUnsupportedSyntax
    addBlock (← ``(Verso.Doc.Block.para #[Verso.Doc.Inline.text "One block."]))
    addBlock (← ``(Verso.Doc.Block.para #[Verso.Doc.Inline.text "Another block."]))
  | _ => throwUnsupportedSyntax

/--
The blocks of a document whose second top-level block is the directive {name}`directive`, followed
by a header, a paragraph, a directive that adds two blocks, and a last paragraph.
-/
def failureBlocks (directive : Name) : String := s!"A first paragraph.

:::{directive}
:::

# A Section

A second paragraph.

:::twoBlocks
:::

A last paragraph.
"

/-- A {lit}`#doc` document with the blocks of {name}`failureBlocks`. -/
def failureInput (directive : Name) : String :=
  "#doc (.none) \"Failure\" =>\n\n" ++ failureBlocks directive

/-- The {lit}`#docs` document {lit}`failureDocs` with the blocks of {name}`failureBlocks`. -/
def failureDocsInput (directive : Name) : String :=
  "#docs (.none) failureDocs \"Failure\" :=\n:::::::\n" ++ failureBlocks directive ++ ":::::::\n"

/--
Elaborates {name}`input` with {name}`directive` and with {name}`succeeding`, and logs the messages
of the first elaboration, whether it defines {name}`docName`, the numbers of definitions under
{name}`docName` in both environments, and whether each definition under {name}`docName` in the first
environment has the same value under the same name in the second.
-/
def compareWithSuccess (input : Name → String) (docName : Name) (directive : Name) :
    CommandElabM Unit := do
  let (failed, msgs) ← elabModuleRest (input directive)
  let (succeeded, _) ← elabModuleRest (input ``succeeding)
  logInfo msgs
  let defs := constantsUnder docName failed
  let defsWithoutFailure := constantsUnder docName succeeded
  let same := defs.all fun n =>
    match failed.find? n, succeeded.find? n with
    | some c, some c' => c.value? == c'.value?
    | _, _ => false
  logInfo m!"The document is defined: {failed.contains docName}\n\
    Definitions under the document's name: {defs.size} of {defsWithoutFailure.size}\n\
    Each is the same as without the failure: {same}"

/-
In a {lit}`#doc` document, a block whose elaboration throws doesn't change the names or values of
the later blocks' definitions, compared with the same document in which that block succeeds, and the
document is still defined.
-/

/--
info: command 2: 5:0: error: The directive fails.
---
info: The document is defined: true
Definitions under the document's name: 5 of 6
Each is the same as without the failure: true
-/
#test_msgs in
#eval do compareWithSuccess failureInput (docName (← getMainModule)) ``failing

/-
The same holds in a {lit}`#docs` document, whose blocks are all elaborated in one command.
-/

/--
info: command 0: 5:0: error: The directive fails.
---
info: The document is defined: true
Definitions under the document's name: 5 of 6
Each is the same as without the failure: true
-/
#test_msgs in
#eval compareWithSuccess failureDocsInput `failureDocs ``failing

/--
A role that elaborates to the name of the declaration that its expander runs under. The text is in a
{lit}`match` on that name, and elaborating the {lit}`match` makes an auxiliary definition. Lean
shares such a definition between {lit}`match` expressions with the same patterns, so the pattern is
the name.
-/
@[role]
def declNameHere : RoleExpanderOf Unit
  | (), _ => do
    let here := Syntax.mkStrLit (toString (← Term.getDeclName?))
    ``(Verso.Doc.Inline.text (match ($here : String) with | $here:str => $here | _ => ""))

/-- A {lit}`#doc` document of two paragraphs that show the declarations they elaborate under. -/
def declNamesInput : String := "#doc (.none) \"Declaration names\" =>

{Verso.Tests.BlockCompilation.declNameHere}[]

{Verso.Tests.BlockCompilation.declNameHere}[]
"

/-
Each block of a {lit}`#doc` document elaborates under the name of its own definition, which differs
between blocks, and the auxiliary definitions made for a block are under that name.
-/

/--
info: Each block runs under the name of a definition under the document's name: true
The two blocks' declaration names differ: true
Each block's definition has auxiliary definitions under it, which differ between the blocks: true
-/
#test_msgs in
#eval do
  let (env, msgs) ← elabModuleRest declNamesInput
  unless msgs.isEmpty do logInfo msgs
  let docName := docName (← getMainModule)
  let doc ← evalDoc env (← getOptions) docName
  let defs := constantsUnder docName env
  let shown := paragraphTexts doc
  let blockDefs := shown.filterMap fun texts =>
    texts[0]? >>= fun shownName => defs.find? fun n => toString (some n) == shownName
  let helpers := blockDefs.map fun (b : Name) => defs.filter fun n => b.isPrefixOf n && n != b
  let disjoint := match helpers[0]?, helpers[1]? with
    | some h, some h' => h.all (!h'.contains ·)
    | _, _ => false
  logInfo m!"Each block runs under the name of a definition under the document's name: \
    {blockDefs.size == 2}\n\
    The two blocks' declaration names differ: {blockDefs[0]? != blockDefs[1]?}\n\
    Each block's definition has auxiliary definitions under it, which differ between the blocks: \
    {helpers.all (!·.isEmpty) && disjoint}"

/-
Adding a block in a context whose document constant name is anonymous fails with an error that gives
the reason, and it adds no constants, because the block definitions of two such documents would
collide.
-/

/--
info: The document has no constant name, so its blocks' definitions can't be created. Give its `DocElabContext` a `docConstName`.
---
info: The environment has no new constants: true
-/
#test_msgs in
#eval show Term.TermElabM Unit from do
  let count (env : Environment) := env.constants.map₂.foldl (init := 0) fun n _ _ => n + 1
  let before := count (← getEnv)
  let ctx ← DocElabContext.fromGenreTerm (← `(Genre.none)) `unused
  let ctx := { ctx with docConstName := .anonymous, declName := .anonymous }
  let block ← ``(Verso.Doc.Block.para #[])
  try
    discard <| PartElabM.run ctx {} (.init .missing .missing) (PartElabM.addBlock block)
  catch e =>
    logInfo e.toMessageData
  logInfo m!"The environment has no new constants: {count (← getEnv) == before}"
