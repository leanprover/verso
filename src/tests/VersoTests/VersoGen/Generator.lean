/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

import Errata
import VersoUtil.Elan
import VersoGen.Edit.Script
import VersoGen.Edit.Shrink
import VersoGen.Edit.Arbitrary
import VersoGen.Server.Check
import VersoTests.VersoGen.Helpers

set_option doc.verso true

/-!
Tests of the generator of Verso documents and edit scripts, which the reuse tests and the language
server checks use as input. These tests matter when changing the generator, concretization, the
genre profiles or the corpus. They also matter when a change to Verso's elaboration or language
server support makes generated documents behave differently.

A failure of a test that runs the generator itself means that generated documents, edits or LSP
edit sequences don't have the form that the reuse tests and the benchmark rely on, so their results
wouldn't mean what they say. A failure of a test that elaborates generated documents
means either that the generator made text that isn't valid for its genre or that Verso fails on
valid text; the test's output shows which documents failed.
-/

open Lean Errata VersoGen.Doc VersoGen.Doc.SurfaceDoc VersoGen.Genre VersoGen.Random
  VersoGen.Text VersoGen.TextEdit VersoGen.Edit VersoGen.Server

namespace Verso.Tests.VersoGen.Generator

/-! # Helpers -/

def note (cs : List Block) : Block := .directive "note" "" cs.toArray

def item (cs : List Block) : Array Block := cs.toArray

def ul (items : List (List Block)) : Block := .ul (items.map item).toArray

def ol (items : List (Array Block)) : Block := .ol items.toArray

def quote (cs : List Block) : Block := .blockquote cs.toArray

def part (title : String) (blocks : List Block) (subParts : List Part := [])
    (metadata : Array (String × String) := #[]) : Part :=
  { title, metadata, blocks := blocks.toArray, subParts := subParts.toArray }

/-- The text of a document after its {lit}`#doc` line. -/
def body (text : String) : String :=
  -- The body is the second of exactly two pieces around the `=>` that ends the `#doc` line and the
  -- blank line after it.
  match (text.split "=>\n\n").fold (init := (0, none)) fun (n, second?) piece =>
      (n + 1, if n == 1 then some piece else second?) with
  | (2, some b) => b.copy
  | _ => text

/-- Applies an edit at a path in a surface document, with the minimal genre profile. -/
def edited (doc : Part) (path : List Nat) (e : Edit) : Option Part :=
  (Zipper.goto doc path >>= applyEdit minimalProfile e).map (·.root)

/-- The body of a surface document's concretized text, with the minimal genre profile. -/
def concretized (doc : Part) : String := body (concretizeDocument minimalProfile doc)

/-! # Lorem Ipsum -/

/-- The generated text starts with the canonical lorem ipsum passage, whatever the seed. -/
@[test]
def loremCanonical : Test := do
  for seed in [42, 7] do
    result s!"seed {seed}" do
      let ws := LoremGen.runWithSeed (words 8) seed
      assertBEq "Lorem ipsum dolor sit amet, consectetur adipiscing elit," ws

/-- The same seed gives the same text, and different seeds give different text. -/
@[test]
def loremDeterminism : Test := do
  let text (seed : Nat) := LoremGen.runWithSeed (words 300) seed
  assertBEq (text 1) (text 1)
  assertNe (text 1) (text 2)

/--
The generated text doesn't contain any character that Verso treats as markup, since concretization
writes it without escaping it.
-/
@[test]
def loremNoMarkup : Test := do
  let text := LoremGen.runWithSeed (do
    let mut out := ""
    for _ in [0:100] do
      out := out ++ (← sentence) ++ (← Lorem.title) ++ (← Lorem.label)
    return out) 3
  for c in "*_[]{}`\\#:>%$!^|~<".chars do
    assertTrue (!text.contains c) s!"the text contains '{c}'"

/-! # Concretization -/

/-- Directives' delimiters are longer than those of the directives nested in them. -/
@[test]
def concretizeDelimiters : Test := do
  let doc := part "T" [note [para "a", note [para "b", note [para "c"]]], note [para "d"]]
  assertBEq ":::::note
a

::::note
b

:::note
c
:::
::::
:::::

:::note
d
:::
"
    (concretized doc)

/--
Code blocks' fences are longer than any sequence of back-ticks that starts a line of their contents.
-/
@[test]
def concretizeFences : Test := do
  let doc := part "T" [Block.code "plain" "" #["x", "```", "  ````y"], Block.code "plain" "" #["z"]]
  assertBEq "`````plain
x
```
  ````y
`````

```plain
z
```
"
    (concretized doc)

/--
The contents of list items, description list items and blockquotes are indented to their content
column, also when they are nested.
-/
@[test]
def concretizeIndentation : Test := do
  let doc := part "T" [
    ol [item [para "a", ul [[para "b"], [Block.code "plain" "" #["c"], note [para "d"]]]],
      item [para "e"]],
    Block.dl #[(#[.text "Term"], #[para "f", para "g"])],
    quote [para "h", para "i"]
  ]
  assertBEq "1. a

   * b

   * ```plain
     c
     ```

     :::note
     d
     :::

2. e

: Term

  f

  g

> h

  i
"
    (concretized doc)

/--
Lists that follow a list of the same kind use the other marker, so the two stay separate lists.
Description lists have no other marker, so documents with neighboring description lists aren't
valid. In prior versions of concretization, neighboring lists were concretized as one list.
-/
@[test]
def concretizeNeighboringLists : Test := do
  result "markers" do
    let doc := part "T" [ul [[para "a"]], ul [[para "b"]], ul [[para "c"]], ol [item [para "d"]],
      ol [item [para "e"]], note [ul [[para "f"]], ul [[para "g"]]]]
    assertBEq "* a

- b

* c

1. d

1) e

:::note
* f

- g
:::
"
      (concretized doc)
  result "description lists" do
    let dl (t : String) : Block := .dl #[(#[.text t], #[para "x"])]
    assertTrue (!minimalProfile.valid (part "T" [dl "a", dl "b"])) "neighboring description lists"
    assertTrue (minimalProfile.valid (part "T" [dl "a", para "p", dl "b"]))
      "separate description lists"

/-- Header levels come from the depth of parts, and parts' metadata blocks follow their headers. -/
@[test]
def concretizeHeaders : Test := do
  let doc := part "T" [para "x"]
    [part "A" [] [part "B" [para "y"]], part "C" [] (metadata := #[("tag", "\"c\"")])]
  assertBEq r#"x

# A

## B

y

# C

%%%
tag := "c"
%%%
"#
    (concretized doc)

/--
Whole documents are concretized with the genre profile's header, the {lit}`#doc` line, metadata and
every kind of inline.
-/
@[test]
def concretizeDocumentWithHeader : Test := do
  let header := minimalProfile.header.foldl (init := "") fun out line => out ++ line ++ "\n"
  let doc := part "A \"quoted\" title" (metadata := #[("draft", "true")]) [
    Block.para #[.text "Some", .emph #[.text "emphasized"], .bold #[.text "bold"],
      .link #[.text "linked"] (.url "https://example.com"), .link #[.text "defined"] (.ref "d"),
      .role "highlight" "" #[.text "role"], .role "term" "" #[.code "t"], .image "alt" "a.png",
      .code "code", .footnote "f"],
    Block.linkDef "d" "https://example.com/d",
    Block.footnoteDef "f" #[.text "A footnote."],
    Block.command "separator" ""
  ]
  assertTrue (minimalProfile.valid doc) "the document is valid"
  let text := concretizeDocument minimalProfile doc
  assertTrue (text.startsWith header) "the text starts with the profile's header"
  assertBEq "#doc (TestGenre) \"A \\\"quoted\\\" title\" =>

%%%
draft := true
%%%

Some _emphasized_ *bold* [linked](https://example.com) [defined][d] {highlight}[role] \
  {term}`t` ![alt](a.png) `code` [^f]

[d]: https://example.com/d

[^f]: A footnote.

{separator}
"
    (text.dropPrefix header).copy

/-! # Surface Document Edits -/

def partsDoc : Part :=
  part "T" [para "a"] [part "A" [para "b"] [part "B" [para "c"]], part "C" [para "d"]]

/--
Part edits and sibling edits of parts have the expected effect on the surface document, and the
edits that would give an invalid document don't apply.
-/
@[test]
def partEdits : Test := do
  let b := part "B" [para "c"]
  let c := part "C" [para "d"]
  result "title" do
    assertBEq (some (part "T" [para "a"] [part "A" [para "b"] [b], part "New" [para "d"]]))
      (edited partsDoc [2] (.setTitle "New"))
  result "metadata" do
    let tagged (v : String) := part "A" [para "b"] [b] (metadata := #[("tag", v)])
    assertBEq (some (part "T" [para "a"] [tagged "\"x\"", c]))
      (edited partsDoc [1] (.addMetadata "tag" "\"x\""))
    let withTag := (edited partsDoc [1] (.addMetadata "tag" "\"x\"")).get!
    assertBEq (some partsDoc) (edited withTag [1] (.removeMetadata "tag"))
    assertBEq (some (part "T" [para "a"] [tagged "\"y\"", c]))
      (edited withTag [1] (.changeMetadata "tag" "\"y\""))
    assertBEq none (edited partsDoc [1] (.addMetadata "unknown" "1"))
  result "insert and delete" do
    assertBEq (some (part "T" [para "a"] [part "A" [para "b"] [b], c, part "D" []]))
      (edited partsDoc [2] (.insertSibling 1 (.part (part "D" []))))
    assertBEq (some (part "T" [para "a"] [part "A" [para "b"] [b]]))
      (edited partsDoc [2] (.deleteSibling 0))
    -- Blocks can't follow a sub-part.
    assertBEq none (edited partsDoc [2] (.insertSibling 1 (.block (para "e"))))
  result "wrap, deparent and reparent" do
    assertBEq (some (part "T" [para "a"] [part "W" [] [part "A" [para "b"] [b], c]]))
      (edited partsDoc [1] (.wrap 0 2 (.part "W")))
    assertBEq (some (part "T" [para "a"] [part "A" [para "b"], b, c]))
      (edited partsDoc [1] (.deparent 0))
    assertBEq (some (part "T" [para "a"] [part "A" [para "b"] [b, c]]))
      (edited partsDoc [1] (.reparent 0))

def blocksDoc : Part :=
  part "T" [note [para "a", para "b", para "c"], ul [[para "x"], [para "y"]],
    quote [para "q"], para "z"]

/--
Sibling edits, directive edits and list item edits have the expected effect on the surface
document, and the edits that would give an invalid document don't apply.
-/
@[test]
def containerEdits : Test := do
  let abc := note [para "a", para "b", para "c"]
  let xy := ul [[para "x"], [para "y"]]
  let q : Block := quote [para "q"]
  result "insert and delete" do
    assertBEq (some (part "T" [note [para "a", para "n", para "b", para "c"], xy, q, para "z"]))
      (edited blocksDoc [0, 0] (.insertSibling 1 (.block (para "n"))))
    assertBEq (some (part "T" [note [para "b", para "c"], xy, q, para "z"]))
      (edited blocksDoc [0, 0] (.deleteSibling 0))
    -- Insertion before the focus gives a new first child.
    assertBEq (some (part "T" [note [para "n", para "a", para "b", para "c"], xy, q, para "z"]))
      (edited blocksDoc [0, 0] (.insertSibling 0 (.block (para "n"))))
    assertBEq (some (part "T" [para "n", abc, xy, q, para "z"]))
      (edited blocksDoc [0] (.insertSibling 0 (.block (para "n"))))
    -- Containers keep at least one child.
    assertBEq none (edited blocksDoc [2, 0] (.deleteSibling 0))
  result "wrap, deparent and reparent" do
    assertBEq
      (some (part "T" [note [quote [para "a", para "b"], para "c"], xy, q, para "z"]))
      (edited blocksDoc [0, 0] (.wrap 0 2 .blockquote))
    assertBEq (some (part "T" [note [ul [[para "a"]], para "b", para "c"], xy, q, para "z"]))
      (edited blocksDoc [0, 0] (.wrap 0 1 .ul))
    assertBEq (some (part "T" [para "a", para "b", para "c", xy, q, para "z"]))
      (edited blocksDoc [0] (.deparent 0))
    assertBEq (some (part "T" [abc, para "x", para "y", q, para "z"]))
      (edited blocksDoc [1] (.deparent 0))
    assertBEq (some (part "T" [abc, xy, quote [para "q", para "z"]]))
      (edited blocksDoc [2] (.reparent 0))
    assertBEq (some (part "T" [abc, ul [[para "x"], [para "y", q]], para "z"]))
      (edited blocksDoc [1] (.reparent 0))
    -- Paragraphs can't have children.
    assertBEq none (edited blocksDoc [3] (.reparent 0))
  result "directives" do
    -- Directives change name and arguments, as the profile allows.
    assertBEq
      (some (part "T"
        [Block.directive "aside" "\"Title\"" #[para "a", para "b", para "c"], xy, q, para "z"]))
      (edited blocksDoc [0] (.changeDirective "aside" "\"Title\""))
    assertBEq none (edited blocksDoc [0] (.changeDirective "unknown" ""))
    -- `aside` may not occur inside a directive.
    assertBEq none
      (edited (part "T" [note [note [para "a"]]]) [0, 0] (.changeDirective "aside" "\"Title\""))
  result "list items" do
    assertBEq (some (part "T" [abc, ul [[para "x"], [para "y"], [para "w"]], q, para "z"]))
      (edited blocksDoc [1, 1] (.insertSibling 1 (.item (item [para "w"]))))
    assertBEq (some (part "T" [abc, ul [[para "y"]], q, para "z"]))
      (edited blocksDoc [1, 0] (.deleteSibling 0))
    assertBEq none (edited blocksDoc [1, 0] (.insertSibling 0 (.block (para "w"))))
    assertBEq (some (part "T" [abc, ul [[para "w"], [para "x"], [para "y"]], q, para "z"]))
      (edited blocksDoc [1, 0] (.insertSibling 0 (.item (item [para "w"]))))

def paraDoc : Part :=
  part "T" [Block.para #[.text "one two three", .emph #[.text "four"], .text "five"]]

/--
Inline edits have the expected effect on a paragraph's inlines, and the edits that would give an
invalid document don't apply.
-/
@[test]
def paragraphEdits : Test := do
  let withInlines (c : Array Inline) : Option Part := some (part "T" [Block.para c])
  let four : Inline := .emph #[.text "four"]
  result "text" do
    assertBEq (withInlines #[.text "one new words two three", four, .text "five"])
      (edited paraDoc [0] (.editText 0 1 0 "new words"))
    assertBEq (withInlines #[.text "three", four, .text "five"])
      (edited paraDoc [0] (.editText 0 0 2 ""))
    assertBEq (withInlines #[four, .text "five"]) (edited paraDoc [0] (.editText 0 0 3 ""))
  result "wrap and unwrap" do
    assertBEq (withInlines #[.bold #[.text "one two three", four], .text "five"])
      (edited paraDoc [0] (.wrapInlines 0 2 (.bold #[])))
    assertBEq
      (withInlines #[.link #[.text "one two three"] (.url "https://example.com"), four,
        .text "five"])
      (edited paraDoc [0] (.wrapInlines 0 1 (.link #[] (.url "https://example.com"))))
    assertBEq (withInlines #[.role "highlight" "" #[.text "one two three"], four, .text "five"])
      (edited paraDoc [0] (.wrapInlines 0 1 (.role "highlight" "" #[])))
    -- Emphasis doesn't nest in emphasis.
    assertBEq none (edited paraDoc [0] (.wrapInlines 1 2 (.emph #[])))
    assertBEq (withInlines #[.text "one two three", .text "four", .text "five"])
      (edited paraDoc [0] (.unwrapInline 1))
    assertBEq none (edited paraDoc [0] (.unwrapInline 0))
  result "insert and remove" do
    assertBEq (withInlines #[.text "one two three", .code "x", four, .text "five"])
      (edited paraDoc [0] (.insertInline 1 (.code "x")))
    assertBEq (withInlines #[.image "i" "i.png", .text "one two three", four, .text "five"])
      (edited paraDoc [0] (.insertInline 0 (.image "i" "i.png")))
    assertBEq (withInlines #[.text "one two three", four]) (edited paraDoc [0] (.removeInline 2))
    -- Footnote uses need a definition.
    assertBEq none (edited paraDoc [0] (.insertInline 0 (.footnote "f")))

/--
Edits of code blocks, block commands, and link and footnote definitions have the expected effect,
and the edits that would give an invalid document don't apply.
-/
@[test]
def leafEdits : Test := do
  let code := Block.code "plain" "" #["a", "b"]
  let command := Block.command "separator" ""
  let use := Block.para #[.link #[.text "l"] (.ref "d")]
  let definition := Block.linkDef "d" "https://example.com"
  let doc := part "T" [code, command, use, definition]
  result "code blocks" do
    assertBEq (some (part "T" [Block.code "plain" "" #["a", "x", "y"], command, use, definition]))
      (edited doc [0]
        (.changeLines { label := "change line", start := 1, count := 1, lines := #["x", "y"] }))
    assertBEq none
      (edited doc [0]
        (.changeLines { label := "remove line", start := 0, count := 2, lines := #[] }))
  result "block commands" do
    assertBEq (some (part "T" [code, Block.command "separator" "x", use, definition]))
      (edited doc [1] (.changeCommandArgs "x"))
  result "definitions" do
    assertBEq (some (part "T" [code, command, use, Block.linkDef "d" "https://example.org"]))
      (edited doc [3] (.changeLinkDef "https://example.org"))
    -- Definitions whose labels are used can't be deleted, and labels are unique.
    assertBEq none (edited doc [3] (.deleteSibling 0))
    assertBEq none
      (edited doc [0] (.insertSibling 0 (.block (Block.linkDef "d" "https://example.com"))))
    let footnote := Block.footnoteDef "n" #[.text "New."]
    assertBEq (some (part "T" [code, command, use, definition, footnote]))
      (edited doc [3] (.insertSibling 1 (.block footnote)))
    -- Definitions occur only among parts' blocks.
    assertBEq none
      (edited (part "T" [note [para "a"]]) [0, 0]
        (.insertSibling 0 (.block (Block.footnoteDef "n" #[.text "New."]))))

/-! # The Edit Generator -/

/--
Edits at paths replay like generated edits, and paths before the previous edit's node are errors,
since edits are recorded in document order.
-/
@[test]
def pathEdits : Test := do
  let edits := [
    (⟨[0, 1], .editText 0 0 0 "new"⟩, SplitStrategy.wholeHunks),
    (⟨[1, 1], .insertSibling 1 (.item (item [para "w"]))⟩, .typing),
    (⟨[3], .editText 0 0 1 "zz"⟩, .garbage)
  ]
  match pathScript minimalProfile blocksDoc edits with
  | .error e => failHere e
  | .ok script =>
    let expected := part "T" [note [para "a", para "new b", para "c"],
      ul [[para "x"], [para "y"], [para "w"]], quote [para "q"], para "zz"]
    assertBEq (some expected) (replayDoc blocksDoc script.recorded)
  -- Paths before the previous edit's node are errors.
  assertTrue (pathScript minimalProfile blocksDoc [(⟨[3], .editText 0 0 1 "zz"⟩, .typing),
    (⟨[0, 1], .editText 0 0 0 "new"⟩, .typing)] matches .error _) "a path before the previous edit"

/--
Generated surface documents stay valid under the generator's edits. Replaying the recorded edits
gives the generator's result, which the theorem {name}`replayDoc_eq_of_editPassWith` proves.
-/
@[test]
def generatedEditsValid : Test := do
  for p in profiles do
    result p.name do
      for seed in [0:30] do
        let (base, edited) := LoremGen.runWithSeed (seed := seed) do
          let base ← genDocument p {}
          let (edited, _) ← generateEdits p {} 20 base
          return (base, edited)
        assertTrue (p.valid base) s!"seed {seed}: the base surface document is valid"
        assertTrue (p.valid edited) s!"seed {seed}: the edited surface document is valid"

/--
Generated documents are valid and are the result of their construction edits, replayed from the
empty document, and in some of them a definition follows its use.
-/
@[test]
def constructionReplays : Test := do
  let definitionsAfterUse ← IO.mkRef 0
  for p in profiles do
    result p.name do
      for seed in [0:30] do
        let params : Params := { topLevelBlocks := 12, parts := 3 }
        let (doc, history) := LoremGen.runWithSeed (constructDocument p params) seed
        assertTrue (p.valid doc) s!"seed {seed}: the document is valid"
        assertBEq (some doc) (replayDoc emptyDocument history)
        for ⟨_, e⟩ in history do
          if let .reference r := e then
            if r.place != .beforeBlock then definitionsAfterUse.modify (· + 1)
  assertTrue ((← definitionsAfterUse.get) > 0) "some definition follows its use"

/--
The edits of generated edit scripts are in document order, and every edit changes the text. In
prior versions of the generator, the traversal continued from a node's first child after an edit of
its children, and some edits left the text unchanged.
-/
@[test]
def editsInDocumentOrder : Test := do
  for p in profiles do
    result p.name do
      for seed in [0:30] do
        let script := generateScript p {} seed 30
        match script.replay with
        | .error e => failHere s!"seed {seed}: {e}"
        | .ok r =>
          let mut prev : String.Pos.Raw := 0
          for i in [0:r.texts.size - 1] do
            let before := r.texts[i]!
            let after := r.texts[i + 1]!
            assertTrue (before != after) s!"seed {seed}: edit {i} changes the text"
            let first := before.firstDiffPos after
            assertTrue (first ≥ prev)
              s!"seed {seed}: edit {i} changes the text at {repr first}, before the previous \
                edit's change at {repr prev}"
            prev := first

/-- The path of the focus after an edit at a path, or {name}`none` if the edit doesn't apply. -/
def focusAfter (doc : Part) (path : List Nat) (e : Edit) : Option (List Nat) :=
  (Zipper.goto doc path >>= applyEdit minimalProfile e).map (·.indexPath)

/--
After an edit, the zipper's focus is where the traversal continues with {lit}`next?`. Each comment
says which node the traversal visits next.
-/
@[test]
def focusAfterEdits : Test := do
  -- An inserted node, whose children come next.
  assertBEq (some [0, 1]) (focusAfter blocksDoc [0, 0] (.insertSibling 1 (.block (para "n"))))
  -- A node inserted before the focus, whose children and then the former focus come next.
  assertBEq (some [0, 0]) (focusAfter blocksDoc [0, 0] (.insertSibling 0 (.block (para "n"))))
  -- A new container, whose first child, the former focus, comes next.
  assertBEq (some [0, 0]) (focusAfter blocksDoc [0, 0] (.wrap 0 2 .blockquote))
  -- Before the node at the index of a deleted one, so that this node comes next.
  assertBEq (some [0]) (focusAfter blocksDoc [0, 0] (.deleteSibling 0))
  assertBEq (some [0, 1]) (focusAfter blocksDoc [0, 2] (.deleteSibling 0))
  assertBEq (some [2, 0]) (focusAfter blocksDoc [3] (.deleteSibling 0))
  -- Before the first former child of a deparented block.
  assertBEq (some [0, 2]) (focusAfter blocksDoc [1] (.deparent 0))
  -- Before the moved node of a reparent, which is in the last item of a list here.
  assertBEq (some [1, 1, 0]) (focusAfter blocksDoc [1] (.reparent 0))
  assertBEq (some [2, 0]) (focusAfter blocksDoc [2] (.reparent 0))
  -- A deparented part, whose blocks come next.
  assertBEq (some [1]) (focusAfter partsDoc [1] (.deparent 0))
  -- A part without sub-parts can't be deparented, and the document's part has no siblings.
  assertBEq none (focusAfter partsDoc [2] (.deparent 0))
  assertBEq none (focusAfter partsDoc [] (.deleteSibling 0))

/--
Reference edits insert a use into a paragraph and its definition at the place that the edit gives,
and the zipper stays at the paragraph. With {name}`DefinitionPlace.documentEnd`, the definition goes
after the last block of the last part.
-/
@[test]
def referenceEdits : Test := do
  let use : Block := .para #[.text "b", .footnote "f"]
  let definition : Block := .footnoteDef "f" #[.text "Note."]
  let edit (place : DefinitionPlace) : Edit :=
    .reference { index := 1, use := .footnote "f", definition, place }
  let b := part "B" [para "c"]
  result "before the block" do
    assertBEq (some (part "T" [para "a"] [part "A" [definition, use] [b], part "C" [para "d"]]))
      (edited partsDoc [1, 0] (edit .beforeBlock))
    assertBEq (some [1, 1]) (focusAfter partsDoc [1, 0] (edit .beforeBlock))
  result "after the block" do
    assertBEq (some (part "T" [para "a"] [part "A" [use, definition] [b], part "C" [para "d"]]))
      (edited partsDoc [1, 0] (edit .afterBlock))
  result "at the end of the document" do
    assertBEq (some (part "T" [para "a"] [part "A" [use] [b], part "C" [para "d", definition]]))
      (edited partsDoc [1, 0] (edit .documentEnd))
    assertBEq (some [1, 0]) (focusAfter partsDoc [1, 0] (edit .documentEnd))
  result "at a part" do
    assertBEq none (edited partsDoc [1] (edit .afterBlock))

/-- The mean number of edits in generated edit scripts, over some seeds. -/
def meanEdits (p : GenreProfile) (editChance : Nat) (seeds : List Nat) : Float :=
  let total := seeds.foldl
    (fun acc seed => acc + (generateScript p {} seed editChance).edits.size) 0
  total.toFloat / seeds.length.toFloat

/--
Higher edit chances give more edits. In prior versions of the generator, the mean number of edits
stopped growing above edit chance 50.
-/
@[test]
def editChanceGivesEdits : Test := do
  for p in profiles do
    result p.name do
      let seeds := List.range' 100 10
      let low := meanEdits p 10 seeds
      let middle := meanEdits p 50 seeds
      let high := meanEdits p 75 seeds
      assertTrue (low < middle && middle < high)
        s!"mean edits {low}, {middle} and {high} at edit chances 10, 50 and 75"

/--
The same genre profile, parameters and seed give the same edit script and the same replayed texts,
and another seed gives another script.
-/
@[test]
def scriptDeterminism : Test := do
  for p in profiles do
    result p.name do
      let s1 := generateScript p {} 11 25
      let s2 := generateScript p {} 11 25
      assertBEq (toJson s1).compress (toJson s2).compress
      assertNe (toJson s1).compress (toJson (generateScript p {} 12 25)).compress
      match s1.replay, s2.replay with
      | .ok r1, .ok r2 => assertBEq r1.texts r2.texts
      | _, _ => failHere "replay failed"

/-- Applying each edit sequence to the text before it gives exactly the text after it. -/
@[test]
def sequencesReachTargets : Test := do
  for p in profiles do
    for seed in [0:20] do
      result s!"{p.name} {seed}" do
        let script := generateScript p {} seed 25
        match script.replay with
        | .error e => failHere e
        | .ok r =>
          for seq in r.sequences, i in [0:r.sequences.size] do
            let text := seq.foldl applyTextEdit r.texts[i]!
            assertTrue (text == r.texts[i + 1]!) s!"edit {i} reaches its target"

/-! # Splitting -/

/-- Applies LSP edits, giving each intermediate text. -/
def states (text : String) (seq : Array Lsp.TextEdit) : Array String :=
  seq.foldl (fun acc e => acc.push (applyTextEdit acc.back! e)) #[text]

/--
Each splitting strategy reaches the new text through its own kind of intermediate texts: whole hunks
in one LSP edit per replacement, typing in edits of at most four characters, and garbage with a
piece of nonsense inserted before each replacement and removed after it.
-/
@[test]
def splitStrategies : Test := do
  let old := concretizeDocument minimalProfile blocksDoc
  let new := concretizeDocument minimalProfile
    ((edited blocksDoc [1] (.wrap 0 2 (.directive "note" ""))).get!)
  let reps := textDiff old new
  assertBEq 2 reps.size
  let splitEdits (strategy : SplitStrategy) (seed : Nat) :=
    toLspEdits old (runWithSeed (splitReplacements strategy reps) seed)
  result "whole hunks" do
    let whole := splitEdits .wholeHunks 0
    assertBEq reps.size whole.size
    assertBEq new (states old whole).back!
  result "typing" do
    -- Some intermediate text has the directive's opening delimiter but not yet its closing one.
    let typed := splitEdits .typing 5
    let typedStates := states old typed
    assertBEq new typedStates.back!
    let longest := reps.foldl (fun m r => max m r.text.length) 0
    assertTrue (typed.all (·.newText.length < longest)) "typed edits are shorter than the hunks"
    let openers (s : String) := (s.split '\n').fold (init := 0) fun n line =>
      if line.startsWith ":::" then n + 1 else n
    assertTrue (typedStates.any (openers · % 2 == 1))
      "an opening delimiter without its closing one"
  result "garbage" do
    let garbage := splitEdits .garbage 5
    let garbageStates := states old garbage
    assertBEq (3 * reps.size) garbage.size
    assertBEq new garbageStates.back!
    assertTrue
      (garbageStates.any fun s => s != old && s != new && garbagePieces.any (s.contains ·))
      "a state with garbage"

/--
No diff or LSP edit splits a multi-byte character: replacements' positions and the ends of LSP
edits' ranges are character positions of the texts that they apply to.
-/
@[test]
def editsAreCharacterAligned : Test := do
  let old := "Grüße aus Köln 🎉 und 東京 am Abend.\nZweite Zeile mit Ärger.\n"
  let new := "Grüße aus München 🎈 und 京都 am Morgen.\nZweite Zeile mit Ölfarbe.\n"
  let reps := textDiff old new
  result "diff" do
    for r in reps do
      assertTrue (r.start.isValid old && r.stop.isValid old)
        s!"a replacement of {repr r.text} is aligned"
  for (name, strategy) in [("whole hunks", SplitStrategy.wholeHunks), ("typing", .typing),
      ("garbage", .garbage)] do
    result name do
      let edits := toLspEdits old (runWithSeed (splitReplacements strategy reps) 3)
      let mut text := old
      for e in edits do
        let fileMap := FileMap.ofString text
        let start := fileMap.lspPosToUtf8Pos e.range.start
        let stop := fileMap.lspPosToUtf8Pos e.range.«end»
        assertTrue (start.isValid text && stop.isValid text)
          s!"an edit of {repr e.newText} is aligned"
        text := applyTextEdit text e
      assertBEq new text

/--
Swapping two consecutive replacements keeps the text that they give when they are applied as LSP
edits, and replacements that touch or overlap aren't swapped. The theorem
{name}`apply?_bind_apply?_of_swap_eq_some` proves that a swap keeps the text for all inputs.
-/
@[test]
def swapKeepsText : Test := do
  let text := "αβγ δεζ ηθι κλμ\n"
  let wordStart (t w : String) : String.Pos.Raw :=
    ((t.toSlice.find? w).map (·.offset)).getD 0
  let rep (t w new : String) : Replacement :=
    let start := wordStart t w
    { start, stop := start + w, text := new }
  let applyAll (t : String) (reps : Array Replacement) : String :=
    (toLspEdits t reps).foldl applyTextEdit t
  let check (first : Replacement) (secondWord new : String) := do
    let second := rep (applyAll text #[first]) secondWord new
    match swap first second with
    | some (second', first') =>
      assertBEq (applyAll text #[first, second]) (applyAll text #[second', first'])
    | none => failHere s!"the replacement of {secondWord} isn't swapped"
  result "second after the first" do
    check (rep text "δεζ" "ΔΕ") "ηθι" "ηθιηθι"
  result "second before the first" do
    check (rep text "κλμ" "") "αβγ" "😀"
  result "touching and overlapping" do
    let first := rep text "δεζ" "ΔΕ"
    let afterFirst := applyAll text #[first]
    assertTrue (swap first (rep afterFirst "ΔΕ" "x")).isNone "an overlapping replacement"
    let firstEnd := wordStart afterFirst " ηθι"
    assertTrue (swap first { start := firstEnd, stop := firstEnd, text := "!" }).isNone
      "a replacement that starts where the first one ends"

/--
Applied as LSP edits, permuted sequences of replacements give the same text as the sequences in
their own order, and some permutation changes the order. The theorem {name}`applyAll?_permute`
proves that a permutation keeps the text for all inputs.
-/
@[test]
def permuteKeepsText : Test := do
  let reordered ← IO.mkRef 0
  for p in profiles do
    result p.name do
      for seed in [0:20] do
        let script := generateScript p {} seed 25
        match script.replay with
        | .error e => failHere s!"seed {seed}: {e}"
        | .ok r =>
          for e in script.edits, i in [0:script.edits.size] do
            let diff := textDiff r.texts[i]! r.texts[i + 1]!
            let reps := runWithSeed (splitReplacements e.split diff) e.splitSeed
            let permutedReps :=
              permute (runWithSeed (swapsToRandomOrder reps.size) (seed + i)) reps
            if permutedReps != reps then reordered.modify (· + 1)
            let permuted := toLspEdits r.texts[i]! permutedReps
            assertBEq r.texts[i + 1]! (permuted.foldl applyTextEdit r.texts[i]!)
  assertTrue ((← reordered.get) > 0) "some permutation changes the order of the replacements"

/--
The {lit}`Arbitrary` instances for surface documents and blocks give valid documents and blocks of
the minimal genre profile.
-/
@[test]
def arbitrarySurfaceDocsValid : Test := do
  result "documents" do
    property (∀ doc : Part, minimalProfile.valid doc) { numInst := 20, maxSize := 20 }
  result "blocks" do
    property (∀ b : Block, minimalProfile.validBlock false b) { numInst := 50 }

/-- Every document that a generated document shrinks to has a shorter concretized text. -/
@[test]
def documentsShrink : Test := do
  for p in profiles do
    result p.name do
      let doc := LoremGen.runWithSeed (genDocument p { topLevelBlocks := 8, parts := 2 }) 5
      let smaller := Plausible.Shrinkable.shrink doc
      assertTrue (!smaller.isEmpty) "the document shrinks"
      let size (d : Part) := (concretizeDocument p d).length
      for d in smaller do
        assertTrue (size d < size doc) "a shrunk document is smaller"

/-! # JSON -/

/-- Surface documents, edit scripts and edit sequences round-trip through JSON. -/
@[test]
def jsonRoundTrip : Test := do
  for p in profiles do
    result p.name do
      let script := generateScript p { proofWeight := 5 } 4 30
      assertBEq (some script.base) ((fromJson? (toJson script.base) : Except String Part).toOption)
      let script' : Except String EditScript := fromJson? (toJson script)
      assertBEq (some (toJson script).compress) (script'.toOption.map (toJson · |>.compress))
      match script.sequences with
      | .error e => failHere e
      | .ok seqs =>
        let seqs' : Except String EditSequences := fromJson? (toJson seqs)
        assertBEq (some (toJson seqs).compress) (seqs'.toOption.map (toJson · |>.compress))

/-! # Elaboration -/

/--
Elaborates Lean files eight at a time and fails if any of them has errors. It first builds the
genre profiles' imports in one process. With Lake's artifact cache, parallel {lit}`lake lean`
processes that each restore the same imports from the cache can fail with permission denied.
-/
def elaborateAll (files : Array System.FilePath) : Test := do
  let imports := (profiles.flatMap (·.imports)).eraseDups
  let build ← IO.Process.output <| Verso.Elan.getSpawnArgsForLake (#["build"] ++ imports.toArray)
  unless build.exitCode == 0 do
    fail "building the documents' imports failed" (detail? := some (build.stdout ++ build.stderr))
  let mut failures := #[]
  for i in [0:(files.size + 7) / 8] do
    let chunk := files.extract (8 * i) (8 * i + 8)
    let tasks ← chunk.mapM fun file => IO.asTask do
      IO.Process.output <| Verso.Elan.getSpawnArgsForLake #["lean", file.toString]
    for file in chunk, t in tasks do
      match t.get with
      | .ok out =>
        unless out.exitCode == 0 do failures := failures.push s!"{file}:\n{out.stdout}{out.stderr}"
      | .error e => failures := failures.push s!"{file}: {e}"
  unless failures.isEmpty do
    fail s!"{failures.size} of {files.size} documents failed to elaborate"
      (detail? := some (failures.foldl (init := "") fun out f => out ++ f ++ "\n"))

/--
Generated documents and the documents that their edit sequences end at elaborate without errors. An
error means that the generator made text that isn't valid for its genre, or that Verso fails on
valid text.
-/
@[test]
def documentsElaborate : Test := do
  let dir := scratchDir "." "documents-elaborate"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll dir
  for p in profiles do
    result p.name do
      let mut files := #[]
      for seed in [0:4] do
        let script := generateScript p { proofWeight := 1 } seed 20
        match script.replay with
        | .error e => failHere s!"seed {seed}: {e}"
        | .ok r =>
          for text in r.texts, i in [0:r.texts.size] do
            let file := dir / s!"{p.name}_{seed}_{i}.lean"
            IO.FS.writeFile file text
            files := files.push file
      elaborateAll files

/--
Every edit script of the benchmark's corpus replays, and every document that it gives elaborates
without errors. A failure after a change to concretization means that the corpus must be generated
again.
-/
@[test]
def corpusElaborates : Test := do
  let dir := scratchDir "." "corpus-elaborates"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll dir
  let scripts ← corpusScripts benchCorpus
  assertTrue (!scripts.isEmpty) "the corpus has edit scripts"
  for file in scripts do
    let name := file.fileStem.getD "script"
    result name do
      let script ← EditScript.load file
      match script.replay with
      | .error e => failHere e
      | .ok r =>
        let mut files := #[]
        for text in r.texts, i in [0:r.texts.size] do
          let out := dir / s!"{name}_{i}.lean"
          IO.FS.writeFile out text
          files := files.push out
        elaborateAll files

/--
Replaying each script of the benchmark's corpus gives the LSP edit sequences recorded in
{lit}`bench/reuse/expected/<script>-sequences.txt`. When reuse results of the corpus change and
these sequences are unchanged, Verso or Lean reuses differently; when the sequences changed too, the
generator or the derivation of edit sequences changed, and the difference in reuse may mean nothing.
-/
@[test]
def corpusSequences : Test := do
  let pos (p : Lsp.Position) := s!"{p.line}:{p.character}"
  for file in ← corpusScripts benchCorpus do
    let name := file.fileStem.getD "script"
    result name do
      let seqs ← EditSequences.load file
      let mut out := s!"{file.fileName.getD ""}\n"
      for (label, seq) in seqs.labels.zip seqs.sequences, i in [0:seqs.sequences.size] do
        out := out ++ s!"edit {i + 1} {label}\n"
        for e in seq do
          out := out ++ s!"  {pos e.range.start}-{pos e.range.«end»} {e.newText.quote}\n"
      goldenFile (benchResults / s!"{name}-sequences.txt") out

/-! # The Language Server's Answers -/

/--
The documents of {lit}`languageServerAgreesWithSurfaceDoc`: a genre profile, a seed and a number of
top-level blocks.
-/
def lspCheckDocuments : List (String × Nat × Nat) :=
  [("minimal", 3, 12), ("minimal", 5, 30), ("minimal", 7, 20), ("manual", 3, 12), ("manual", 5, 30),
   ("manual", 7, 20)]

/-- The golden file of {lit}`languageServerAgreesWithSurfaceDoc`. -/
def lspChecksGolden : System.FilePath :=
  "src" / "tests" / "integration" / "language-server-answers" / "lsp-checks.txt"

/--
The language server check reports folding ranges that cross, and not ranges that are nested or
disjoint.
-/
@[test]
def foldCrossingsReported : Test := do
  result "crossing" do
    assertBEq 1 (foldCrossings #[(none, 2, 5), (none, 4, 8)]).size
  result "nested or disjoint" do
    assertBEq 0 (foldCrossings #[(none, 2, 8), (none, 4, 5), (none, 9, 10)]).size

/--
The language server check accepts a {lit}`null` semantic token response as no tokens, and any other
response only when it decodes as semantic tokens with five numbers for each token.
-/
@[test]
def semanticTokenResponsesDecoded : Test := do
  let withData (data : Json) := Json.mkObj [("data", data)]
  let rejects (j : Json) : TestM String := do
    match semanticTokenData j with
    | .ok data => failHere s!"the response was accepted with the data {data}"
    | .error e => return e
  result "two tokens" do
    match semanticTokenData (withData (toJson #[0, 1, 2, 0, 0, 1, 0, 3, 0, 0])) with
    | .ok data => assertBEq 10 data.size
    | .error e => failHere e
  result "no data" do discard <| rejects (Json.mkObj [])
  result "data that aren't numbers" do
    discard <| rejects (withData (toJson #["a", "b", "c", "d", "e"]))
  result "null" do
    match semanticTokenData .null with
    | .ok data => assertBEq 0 data.size
    | .error e => failHere e
  result "data length not a multiple of five" do
    assertBEq "the data has 7 numbers, which isn't a multiple of five"
      (← rejects (withData (toJson #[0, 1, 2, 0, 0, 1, 0])))

/--
When a generated document is opened, the language server's document symbols, folding ranges,
highlights, hovers and semantic tokens agree with its surface document, and the answers that the
checks allow match {name}`lspChecksGolden`. In prior versions of Verso, highlighting at a use of a
link or footnote gave only that use.
-/
@[test]
def languageServerAgreesWithSurfaceDoc : Test := do
  let report ← IO.mkRef ""
  for (profileName, seed, blocks) in lspCheckDocuments do
    let name := s!"{profileName}-{seed}-{blocks}"
    result name do
      let some p := profile? profileName | failHere s!"unknown genre profile {profileName}"
      let script := generateScript p { topLevelBlocks := blocks, parts := blocks / 5 } seed 0
      let doc := scratchDir "." "lsp-checks" / s!"{name}.lean"
      let (text, ok) ← checkAnswers "." doc p script.base name
      report.modify (· ++ text)
      unless ok do
        fail "a check of the language server's answers failed" (detail? := some text)
  goldenFile lspChecksGolden (← report.get)

/--
info: 'VersoGen.Edit.replayDoc_eq_of_editPassWith' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#test_msgs in
#print axioms replayDoc_eq_of_editPassWith

/--
info: 'VersoGen.TextEdit.apply?_bind_apply?_of_swap_eq_some' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#test_msgs in
#print axioms apply?_bind_apply?_of_swap_eq_some

/--
info: 'VersoGen.TextEdit.applyAll?_permute' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#test_msgs in
#print axioms applyAll?_permute
