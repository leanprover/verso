/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import VersoGen.Edit.Script
import VersoGen.Server.Reuse
import VersoTests.VersoGen.Helpers
import VersoTests.VersoGen.BlockOutline
import Verso.Doc.Concrete.ReuseMeasure

set_option doc.verso true

/-!
Tests of the reuse measure and of the language server's reuse. The reuse measure finds how much of
a Verso document the server reuses after an edit. Golden files record the server's reuse, and they
are the baseline that work on incremental elaboration is measured against and its regression test.
These tests matter when changing the reuse measure or its measurement in the language server and
when a change to Verso or Lean changes what the server reuses.

The reuse measure reads the block outline of each top-level block from the trace class
`Elab.Verso.blocks` and the {lit}`reuse stopped` messages from {option}`trace.Elab.reuse`. From them
it computes the reused size and the reusable size after each edit sequence. A failure of a test that
calls the measure directly means that the measure doesn't follow its rules. A difference from a
golden file is a change in the server's reuse, which is reviewed whether it is better or worse.
-/

open Lean Errata Verso.Doc.Concrete.ReuseMeasure VersoGen.Doc VersoGen.Doc.SurfaceDoc
  VersoGen.Genre VersoGen.Random VersoGen.TextEdit VersoGen.Edit VersoGen.Server

open Verso.Doc.Concrete (BlockOutline BlockElabOutline)

open Verso.Tests.VersoGen.BlockOutline (outline traceMessage)

namespace Verso.Tests.VersoGen.Reuse

/-! # The Reuse Computation -/

/--
The reusable size after an edit that changes {name}`before` into {name}`after`, both parsed as
Verso's concrete syntax. The edit starts at the first character where the texts differ.
-/
def reusableAfterEdit (before after : String) : IO Nat := do
  let result := measure (← outline before) (before.firstDiffPos after) #[]
    (after := ← outline after)
  return result.reusable

/--
Paragraphs that move from one item of a list or a description list to the next aren't reusable,
even though their ranges and digests stay the same.
-/
@[test]
def paragraphMovesToNextItem : Test := do
  let paras (text : String) : IO (Array (String.Pos.Raw × String.Pos.Raw × String)) := do
    return (← outline text).flatMap BlockOutline.flatten
      |>.filter (·.kind == ``Lean.Doc.Parser.Block.para)
      |>.map fun b => (b.startPos, b.stopPos, b.digest)
  let itemSizes (text : String) : IO (Array Nat) := do
    return (← outline text).flatMap (·.children.map (·.children.size))
  result "list" do
    -- A list marker replaces the indentation before C, so C moves into a new second item.
    let before := "* A\n\n  B\n\n  C\n"
    let after := "* A\n\n  B\n\n* C\n"
    assertBEq (← paras before) (← paras after)
    assertBEq #[3] (← itemSizes before)
    assertBEq #[2, 1] (← itemSizes after)
    assertBEq 2 (← reusableAfterEdit before after)
  result "description list" do
    -- The paragraph Two becomes the term of a new item, so B moves into that item.
    let before := ": One\n\n  A\n\n  Two\n\n  B\n"
    let after := ": One\n\n  A\n\n: Two\n\n  B\n"
    assertBEq (← paras before).back? (← paras after).back?
    assertBEq #[3] (← itemSizes before)
    assertBEq #[1, 1] (← itemSizes after)
    assertBEq 1 (← reusableAfterEdit before after)

/--
A sample text for {lit}`reuseComputation`, whose block outline has six block syntax nodes. The
position just after the quoted paragraph is still inside the nested directive, whose closing
delimiter is on the next line.
-/
def measureSample : String :=
  "First paragraph.

::::note
Second paragraph.

:::note
Quoted paragraph.
:::
::::

Last paragraph.
"

/--
The bounds of the first line of {name}`text` that starts with {name}`lineStart`: the position of its
first character and the position after its last character, before its line break.
-/
def lineBounds (text lineStart : String) : String.Pos.Raw × String.Pos.Raw := Id.run do
  let mut pos : String.Pos.Raw := 0
  for line in text.split '\n' do
    if line.startsWith lineStart then return (pos, pos + line)
    pos := pos + line + '\n'
  panic! s!"no line starts with {lineStart.quote}"

/--
The position of the first {name}`word` in the first line of {name}`text` that starts with
{name}`lineStart`.
-/
def wordIn (text lineStart word : String) : String.Pos.Raw :=
  let (start, stop) := lineBounds text lineStart
  let line := text.slice! (text.pos! start) (text.pos! stop)
  match line.find? word with
  | some pos => start + line.sliceTo pos
  | none => panic! s!"no {word.quote} in the line that starts with {lineStart.quote}"

/--
The reuse measure finds the reuse boundary and counts the largest block syntax nodes that end at or
before it or that the edit leaves unchanged, by the rules that the names of its results state. The
positions are places in {name}`measureSample`.
-/
@[test]
def reuseComputation : Test := do
  let text := measureSample
  let blocks ← outline text
  let inFirst := wordIn text "First" "paragraph"
  let firstEnd := (lineBounds text "First").2
  let outerStart := (lineBounds text "::::note").1
  let secondEnd := (lineBounds text "Second").2
  let innerStart := (lineBounds text ":::note").1
  let inQuoted := wordIn text "Quoted" "paragraph"
  let afterQuoted := (lineBounds text "Quoted").2 + '\n'
  let lastStart := (lineBounds text "Last").1
  let inLast := wordIn text "Last" "paragraph"
  result "the latest reuse stopped message at or before the edit is the boundary" do
    assertBEq { reused := 1, reusable := 2, total := 6, boundarySource := .reuseStopped }
      (measure blocks inQuoted #[inFirst, outerStart, inLast])
    assertBEq { reused := 2, reusable := 2, total := 6, boundarySource := .reuseStopped }
      (measure blocks inQuoted #[innerStart])
  result "without messages, the start of the enclosing top-level block is the boundary" do
    assertBEq { reused := 5, reusable := 5, total := 6, boundarySource := .enclosingBlock }
      (measure blocks inLast #[])
  result "without a new message at or before the edit, the earliest after it is the boundary" do
    assertBEq { reused := 5, reusable := 2, total := 6, boundarySource := .reuseStopped }
      (measure blocks inQuoted #[inLast, lastStart])
    assertBEq { reused := 5, reusable := 2, total := 6, boundarySource := .reuseStopped }
      (measure blocks inQuoted #[outerStart, lastStart] (newStops := #[lastStart]))
  result "new messages after the edit win over earlier messages that aren't new" do
    assertBEq { reused := 5, reusable := 2, total := 6, boundarySource := .reuseStopped }
      (measure blocks inQuoted #[outerStart, afterQuoted, lastStart] (newStops := #[lastStart]))
  result "without new messages, the earliest message after the edit is the boundary" do
    -- The boundary is after the quoted paragraph and before the end of the nested directive, so
    -- the reused size counts the paragraph but not the directive.
    assertBEq { reused := 3, reusable := 2, total := 6, boundarySource := .reuseStopped }
      (measure blocks inQuoted #[outerStart, afterQuoted, lastStart] (newStops := #[]))
  result "new messages at or before the edit make the latest one there the boundary" do
    assertBEq { reused := 1, reusable := 2, total := 6, boundarySource := .reuseStopped }
      (measure blocks inQuoted #[inFirst, outerStart, inLast] (newStops := #[outerStart, inLast]))
  result "without messages after the edit, the latest one at or before it is the boundary" do
    assertBEq { reused := 1, reusable := 2, total := 6, boundarySource := .reuseStopped }
      (measure blocks inQuoted #[inFirst, outerStart] (newStops := #[]))
  result "edits before the first block reuse nothing" do
    assertBEq { reused := 0, reusable := 0, total := 6, boundarySource := .enclosingBlock }
      (measure blocks 0 #[])
  result "blocks that end where the edit starts are reusable only if they are unchanged" do
    -- The edit at the end of the first paragraph either extends it or adds a paragraph after it.
    let extended ← outline (text.replace "First paragraph." "First paragraph. More text.")
    assertBEq { reused := 0, reusable := 0, total := 6, boundarySource := .enclosingBlock }
      (measure blocks firstEnd #[] (after := extended))
    let added ← outline (text.replace "First paragraph." "First paragraph.\n\nA new paragraph.")
    assertBEq { reused := 0, reusable := 1, total := 6, boundarySource := .enclosingBlock }
      (measure blocks firstEnd #[] (after := added))
    assertBEq { reused := 0, reusable := 0, total := 6, boundarySource := .enclosingBlock }
      (measure blocks firstEnd #[])
  result "nested blocks that end where the edit starts are reusable only if unchanged" do
    -- The edit is at the end of the second paragraph, inside the outer directive, and the reuse
    -- boundary is at the start of the outer directive.
    let nestedExtended ← outline (text.replace "Second paragraph." "Second paragraph. More text.")
    assertBEq { reused := 1, reusable := 1, total := 6, boundarySource := .reuseStopped }
      (measure blocks secondEnd #[outerStart] (after := nestedExtended))
    let nestedAdded ← outline (text.replace "Second paragraph." "Second paragraph.\n\nA new one.")
    assertBEq { reused := 1, reusable := 2, total := 6, boundarySource := .reuseStopped }
      (measure blocks secondEnd #[outerStart] (after := nestedAdded))
  result "blocks with the same range and size but other text have changed" do
    let sameLengthReplacement ← outline (text.replace "First paragraph." "Other paragraph.")
    assertBEq { reused := 0, reusable := 0, total := 6, boundarySource := .enclosingBlock }
      (measure blocks firstEnd #[] (after := sameLengthReplacement))
  result "edits after the last top-level block change its syntax" do
    let appended ← outline (text ++ "\nA paragraph after the last one.\n")
    assertBEq { reused := 5, reusable := 5, total := 6, boundarySource := .enclosingBlock }
      (measure blocks text.rawEndPos #[] (after := appended))
  result "edits after a nested block that ends the last top-level block change its syntax" do
    -- The last top-level block is a blockquote, whose last paragraph ends where it ends.
    let quoteText := "First paragraph.\n\n> Second paragraph.\n\n  Third paragraph.\n"
    let quoteBlocks ← outline quoteText
    let quoteAppended ← outline (quoteText ++ "\nA paragraph after the quote.\n")
    assertBEq { reused := 1, reusable := 2, total := 4, boundarySource := .enclosingBlock }
      (measure quoteBlocks quoteText.rawEndPos #[] (after := quoteAppended))

/--
{lit}`reuse stopped` messages are new when the block that they start was elaborated again, and other
{lit}`reuse stopped` messages are new when no earlier message has the same text at the same
position. The language server reports only new messages after an edit in the documents of
{lit}`serverReuse`, so this rule is checked on given messages.
-/
@[test]
def reuseStoppedIsNew : Test := do
  let blocks ← outline "A paragraph.\n"
  let trace (time : String) : TextDiagnostic :=
    { pos := ⟨0, 0⟩, severity := "info", text := traceMessage blocks time }
  let stop : TextDiagnostic := { pos := ⟨0, 0⟩, severity := "info", text := "reuse stopped" }
  let atBlock := blocks[0]!.startPos
  let elsewhere := blocks[0]!.stopPos
  result "block not elaborated again" do
    let diags := #[trace "1990-01-01 00:00:00.000000", stop]
    assertTrue (!isNew diags diags stop atBlock) "the message isn't new"
  result "block elaborated again" do
    let prev := #[trace "1990-01-01 00:00:00.000000", stop]
    let diags := #[trace "1990-01-01 00:00:01.000000", stop]
    assertTrue (isNew prev diags stop atBlock) "the message is new"
  result "no block" do
    assertTrue (!isNew #[stop] #[stop] stop elsewhere) "a repeated message isn't new"
    assertTrue (isNew #[] #[stop] stop elsewhere) "a message that wasn't there before is new"

/-! # Reuse in the Language Server -/

/--
A document with top-level paragraphs, a directive that contains a list, a list whose first item has
two paragraphs, and a description list. {lit}`reuseCases` lists its block sizes.
-/
def reuseDoc : Part := {
  title := "Reuse"
  blocks := #[
    para "Oaks grow slowly over many years.",
    para "Birches grow faster than oaks.",
    .directive "note" "" #[para "Mycelium spreads through the soil.",
      para "Fungi link the roots of nearby trees.",
      .ul #[#[para "Threads carry sugar from tree to tree."],
        #[para "Mushrooms appear after the rain."]]],
    para "Maples glow red in the fall.",
    .ul #[#[para "Leaves lose their green as the days grow short.",
        para "Poplars stand bare for months."],
      #[para "Pines keep their needles all year."]],
    .dl #[(#[.text "Sap"], #[para "Sap rises in the trunk each spring."])],
    para "Seeds sprout when the ground warms."
  ]
}

/-- The edit sequence of one edit at a path on {name}`reuseDoc`. -/
def pathCase (path : List Nat) (e : Edit) (split : SplitStrategy := .wholeHunks) :
    Except String EditSequences := do
  (← pathScript minimalProfile reuseDoc [(⟨path, e⟩, split)]).sequences

/-- Where an insertion goes, by the first line that starts with some text. -/
inductive Site where
  /-- The end of the line. -/
  | endOf (lineStart : String)
  /-- The start of the line. -/
  | startOf (lineStart : String)
  /-- The start of the line before it. -/
  | lineBefore (lineStart : String)
  /-- The end of the text. -/
  | textEnd

/--
The index and the contents of the first line of {name}`text` that starts with {name}`lineStart`.
-/
def lineIndex (text lineStart : String) : Except String (Nat × String.Slice) := do
  let mut i := 0
  for line in text.split '\n' do
    if line.startsWith lineStart then return (i, line)
    i := i + 1
  throw s!"no line starts with {lineStart}"

def Site.position (site : Site) (text : String) : Except String String.Pos.Raw := do
  let fileMap := FileMap.ofString text
  match site with
  | .textEnd => return text.rawEndPos
  | .endOf l =>
    let (n, line) ← lineIndex text l
    return fileMap.lspPosToUtf8Pos ⟨n, 0⟩ + line
  | .startOf l => return fileMap.lspPosToUtf8Pos ⟨(← lineIndex text l).1, 0⟩
  | .lineBefore l => return fileMap.lspPosToUtf8Pos ⟨(← lineIndex text l).1 - 1, 0⟩

/--
Edit sequences on the concretized text of {name}`reuseDoc`. Each sequence has a label and inserts
texts at sites, in order, with one LSP edit for each text. The sequences whose labels are in
{name}`permuted` are reordered before they become LSP edits: {name}`swapsToRandomOrder` draws
exchanges from the sequence's index as a seed, and {name}`permute` applies them.
-/
def rawCase (seqs : List (String × List (Site × String))) (permuted : List String := []) :
    Except String EditSequences := do
  let base := concretizeDocument minimalProfile reuseDoc
  let mut text := base
  let mut sequences := #[]
  for (label, inserts) in seqs, i in [0:seqs.length] do
    let before := text
    let mut reps := #[]
    for (site, new) in inserts do
      let pos ← site.position text
      let r : Replacement := { start := pos, stop := pos, text := new }
      text := (r.apply? text).getD text
      reps := reps.push r
    if permuted.contains label then
      reps := permute (runWithSeed (swapsToRandomOrder reps.size) i) reps
    sequences := sequences.push (toLspEdits before reps)
  return { base, sequences, labels := seqs.toArray.map (·.1) }

/-- What a case of {lit}`serverReuse` records from the language server. -/
inductive Record where
  /-- The reuse after each edit sequence, from {name}`reuseReport`. -/
  | reuse (opts : ReuseOptions := {})
  /-- The snapshot tree of the base document's first elaboration. -/
  | snapshotTree

/-- The directory of the golden files of {lit}`serverReuse`. -/
def serverReuseGoldens : System.FilePath := "src" / "tests" / "integration" / "server-reuse"

/--
The cases of {lit}`serverReuse`: a name, the edit sequences and what the case records. Each case's
report is compared with the golden file {lit}`<name>.txt` in {name}`serverReuseGoldens`.

The input is {name}`reuseDoc` and edits on it. Its top-level blocks and their block sizes are: the
paragraphs Oaks (1) and Birches (1), the directive (8: two paragraphs and a list of two items with
one paragraph each), the paragraph Maples (1), the list (6: an item with the paragraphs Leaves and
Poplars, and an item with the paragraph Pines), the description list (3: an item with the paragraph
Sap) and the paragraph Seeds (1). The total is 21.

Each result line gives the reused size and the reusable size, each with its percentage of the total,
and then the total. The reused size is what the language server reused, as its {lit}`reuse stopped`
messages show. The reusable size is what the edit leaves unchanged. When the reused size is below
the reusable size, the difference is reuse that the server misses. A reused size above the
reusable size means that the server reused a block whose syntax changed, or that the measure is
wrong. A change in a number is a change in reuse to review, whether it is better or worse.
-/
def reuseCases : List (String × Except String EditSequences × Record) := [
  -- Edits in a top-level paragraph reuse every block before it. Three words inserted into the
  -- paragraph Maples give reused and reusable sizes of 10, for Oaks, Birches and the directive.
  ("top-level", pathCase [3] (.editText 0 1 0 "in the north"), .reuse),
  -- Edits inside a directive make the server elaborate the whole directive again. Three words
  -- inserted into the directive's second paragraph give reused 2 and reusable 3. The directive's
  -- first paragraph ends before the edit, so it is reusable, but the server doesn't reuse it.
  ("nested-directive", pathCase [2, 1] (.editText 0 1 0 "in the north"), .reuse),
  -- Edits inside a list item make the server elaborate the whole list again. Three words inserted
  -- into the paragraph Poplars, in the first item of the top-level list, give reused 11 and
  -- reusable 12. The paragraph Leaves ends before the edit, so it is reusable, but the server
  -- doesn't reuse it.
  ("nested-list-item", pathCase [4, 0, 1] (.editText 0 1 0 "in the north"), .reuse),
  -- Edits before the `#doc` line reuse nothing. A comment line inserted there gives reused and
  -- reusable 0.
  ("header", rawCase [("raw", [(.startOf "#doc", "-- A comment before the document\n")])],
    .reuse),
  -- Spaces at the end of a paragraph's line change that paragraph. Three spaces appended to the
  -- paragraph Birches give reused and reusable 1, for Oaks, because the range of Birches grows to
  -- include the spaces.
  ("trailing-whitespace", rawCase [("raw", [(.endOf "Birches", "   ")])], .reuse),
  -- Paragraphs that end where an edit starts have changed, so they aren't reusable. Three edit
  -- sequences each append words to a paragraph: Maples, the directive's second paragraph, and
  -- Poplars in the list. The sizes are those of `top-level`, `nested-directive` and
  -- `nested-list-item`: 10 and 10, then 2 and 3, then 11 and 12. Each sequence is measured against
  -- the block outline after the previous one. In prior versions of the reuse measure, a block that
  -- ended where the edit started counted as reusable.
  ("end-of-block", rawCase [
    ("end of a paragraph", [(.endOf "Maples", " each year")]),
    ("end of a paragraph in a directive", [(.endOf "Fungi", " at last")]),
    ("end of a paragraph in a list item", [(.endOf "  Poplars", " in winter")])
  ], .reuse),
  -- The edit position of each edit sequence in a session is the first character that the sequence
  -- changed. The session has eleven edit sequences, and the total grows as new blocks appear. The
  -- results, in order:
  -- 1. The end of Maples: reused and reusable 10, the blocks before Maples.
  -- 2. The end of Seeds, the last block: reused and reusable 20, every block but Seeds.
  -- 3. The end of the directive's second paragraph: reused 2 and reusable 3, as in
  --    `nested-directive`.
  -- 4. Seeds, then Birches: the edit starts at the earlier region, so reused and reusable 1.
  -- 5. A new paragraph after Birches: reused and reusable 2. Birches ends where the edit starts and
  --    is unchanged.
  -- 6. A new paragraph in the directive, with a total of 22: reused 3, the three paragraphs before
  --    the directive, and reusable 5, which adds the directive's two paragraphs.
  -- 7. Oaks, then Seeds, with a total of 23: the edit starts in the first block, so 0.
  -- 8. A blank line after the directive: reused 3 and reusable 12. The directive's syntax ends
  --    before the blank line, but the server elaborates it again.
  -- 9. A new paragraph at the end: reused and reusable 22. The last block's syntax changes, since
  --    another block follows it.
  -- 10. The end of Poplars, with a total of 24: reused 13 and reusable 14, as in
  --     `nested-list-item`.
  -- 11. The end of Maples again: reused and reusable 12.
  ("edit-sequences", rawCase [
    ("end of a paragraph", [(.endOf "Maples", " each year")]),
    ("end of the last block", [(.endOf "Seeds", " again")]),
    ("in a directive", [(.endOf "Fungi", " slowly")]),
    ("two regions, late then early", [(.endOf "Seeds", " often"), (.endOf "Birches", " too")]),
    ("new block after a paragraph", [(.endOf "Birches", "\n\nBeeches grow in the shade.")]),
    ("new block in a directive", [(.endOf "Fungi", "\n\nMoss grows on the bark.")]),
    ("two regions, early then late",
      [(.endOf "Oaks", " quickly"), (.endOf "Seeds", " by night")]),
    ("blank line between blocks", [(.lineBefore "Maples", "\n")]),
    ("new block at the end", [(.textEnd, "\nThe first frost ends the season.\n")]),
    ("in a list item", [(.endOf "  Poplars", " in winter")]),
    ("end of a paragraph again", [(.endOf "Maples", " once more")])
  ], .reuse),
  -- The order of an edit sequence's LSP edits shows in the reuse after each of them. The two edits
  -- append words to Oaks and to Poplars, and `permute` puts the edit to Poplars first. After it,
  -- the reused size is 11 and the reusable size 12, as in `nested-list-item`; after the edit to
  -- Oaks, both are 0. In the order of the sites, the first result would be 0.
  ("permuted", rawCase [
    ("two regions, permuted", [(.endOf "Oaks", " slowly"), (.endOf "  Poplars", " in spring")])
  ] (permuted := ["two regions, permuted"]), .reuse { each := true }),
  -- The edit position is the first character that changed, even when the LSP edit starts earlier.
  -- Birches changes, and then a copy of the changed paragraph is pasted at the end of Oaks. The
  -- pasted text begins with a copy of the text that follows it, so the first changed byte is after
  -- the first copy of Birches. The sizes are 1 and 1, then 2 and 2, because the server reuses the
  -- first copy. In prior versions of the reuse measure, the edit position was the start of the LSP
  -- edit, and the second result was reused 2 and reusable 1.
  ("pasted-copy", rawCase [
    ("change a paragraph", [(.endOf "Birches", " Their bark is thin.")]),
    ("paste a copy of it before it",
      [(.endOf "Oaks", "\n\nBirches grow faster than oaks. Their bark is thin.")])
  ], .reuse),
  -- `reuse stopped` messages are new when their block is elaborated again, even with the same text
  -- and position as an earlier message. The first edit sequence inserts a blank line after the
  -- directive. The second inserts another one there and appends a sentence to Seeds. Both results
  -- are reused 2 and reusable 10: the server elaborates the directive again, although its syntax
  -- ends before the edit. In the second sequence, the directive's `reuse stopped` message has the
  -- same text and position as after the first, and it is new because the directive's
  -- `Elab.Verso.blocks` message has a new time. In prior versions of the reuse measure, a message
  -- was new only if its text differed from every earlier message, and the second result was reused
  -- 20, every block before Seeds.
  ("repeated-reuse-stopped-later-edit", rawCase [
    ("blank line after a directive", [(.lineBefore "Maples", "\n")]),
    ("again, then an edit at the end",
      [(.lineBefore "Maples", "\n"), (.endOf "Seeds", " Frost returns each winter.")])
  ], .reuse),
  -- Typing an edit gives the same reuse as making it at once and the same diagnostics as a cold
  -- elaboration. Four words are typed into Maples in six LSP edits, with the typing splitting
  -- strategy. Each intermediate state and the final result give reused and reusable 10, as in
  -- `top-level`. At the end, the session's diagnostics match those of a cold elaboration, with
  -- `reuse stopped` messages and the times of `Elab.Verso.blocks` messages left out.
  ("typed", pathCase [3] (.editText 0 1 0 "in the far north") .typing,
    .reuse { each := true, cold := true }),
  -- The first elaboration of `reuseDoc` gives one command snapshot for each top-level block, at
  -- lines 7, 9, 11, 21, 23, 29 and 33, besides one for the `open` command, one for the `#doc` line
  -- and one at the end of the text. The language server reuses whole command snapshots, so a change
  -- in this tree changes what the server can reuse, and the reuse goldens need review with it.
  ("snapshot-tree", pathCase [3] (.editText 0 1 0 "in the north"), .snapshotTree)
]

/--
Reuse reports are read back from their text, also when a diagnostic of the cold comparison has a
later line that starts like a new diagnostic.
-/
@[test]
def reuseReportRoundTrip : Test := do
  let final : EditReuse :=
    { result := { reused := 0, reusable := 1, total := 1, boundarySource := .enclosingBlock },
      errors := 2 }
  let report : ReuseReport :=
    { baseTotal := 1, baseErrors := 0, sequences := #[{ label := "an edit", final }],
      cold? := some { onlyWarm := #["1:0 error: a\n  - b"], onlyCold := #["2:0 error: c\n  + d"] } }
  match ReuseReport.parse report.render with
  | .ok parsed => assertBEq report parsed
  | .error e => failHere e

/--
A diagnostic that occurs twice among the session's diagnostics and once among the cold
elaboration's, or the other way around, is a difference in the cold comparison.
-/
@[test]
def coldComparisonCountsDuplicates : Test := do
  let d : TextDiagnostic := { pos := ⟨0, 0⟩, severity := "error", text := "unknown identifier" }
  let report (c : ColdComparison) : ReuseReport :=
    { baseTotal := 1, baseErrors := 1, sequences := #[], cold? := some c }
  result "twice in the session" do
    let c := ColdComparison.of #[d, d] #[d]
    assertBEq ({ onlyWarm := #[d.describe] } : ColdComparison) c
    assertBEq "base: total 1 errors 1\ncold: diagnostics differ\n  - \
      1:0 error: unknown identifier\n" (report c).render
  result "twice in the cold elaboration" do
    let c := ColdComparison.of #[d] #[d, d]
    assertBEq ({ onlyCold := #[d.describe] } : ColdComparison) c
    assertBEq "base: total 1 errors 1\ncold: diagnostics differ\n  + \
      1:0 error: unknown identifier\n" (report c).render

/--
Edit sequences with fewer labels than sequences are an error, both when they are read from a file
and when the language server replays them.
-/
@[test]
def mismatchedLabelsRejected : Test := do
  let seqs : EditSequences := { base := "", sequences := #[#[], #[]], labels := #["an edit"] }
  let dir := scratchDir "." "mismatched-labels"
  let rejects (file : System.FilePath) (act : IO Unit) : TestM Unit := do
    match ← act.toBaseIO with
    | .ok () => failHere "the edit sequences were accepted"
    | .error e =>
      assertBEq s!"{file}: the numbers of edit sequences (2) and labels (1) differ" (toString e)
  result "load" do
    let file := dir / "sequences.json"
    saveJson seqs file
    rejects file do discard <| EditSequences.load file
  result "reuseReport" do
    let doc := dir / "document.lean"
    rejects doc do discard <| reuseReport "." doc seqs

/--
How the reuse in {name}`after` differs from the reuse in {name}`before`.

The result starts with the base document's total size and errors when they differ. It lists each
edit sequence whose results changed, with its reused and reusable sizes before and after and the
other results that differ. A line of the same kind follows for each LSP edit whose results differ.
Edit sequences that only one of the reports has are listed as such. Then come the diagnostics that
only one of the two cold comparisons has. The last line counts the sequences whose missed reuse (the
reusable size minus the reused size) shrank, grew or stayed the same. It ends with the total reused
size before and after.
-/
def reuseChange (before after : ReuseReport) : String := Id.run do
  let change {α} [ToString α] [BEq α] (what : String) (b a : α) : String :=
    if b == a then "" else s!", {what} {b} → {a}"
  let sizes (b a : EditReuse) : String :=
    s!"reused {b.result.reused} → {a.result.reused}, \
      reusable {b.result.reusable} → {a.result.reusable}"
  -- The changes of a result besides its reused and reusable sizes
  let others (b a : EditReuse) : String :=
    change "total" b.result.total a.result.total ++
    change "boundary" b.result.boundarySource.describe a.result.boundarySource.describe ++
    change "errors" b.errors a.errors
  let missed (r : EditReuse) : Int := (r.result.reusable : Int) - r.result.reused
  let mut out := ""
  if before.baseTotal != after.baseTotal || before.baseErrors != after.baseErrors then
    out := out ++ s!"base: total {before.baseTotal} → {after.baseTotal}, errors \
      {before.baseErrors} → {after.baseErrors}\n"
  let mut improved := 0
  let mut regressed := 0
  let mut sameMissed := 0
  for i in [0:max before.sequences.size after.sequences.size] do
    match before.sequences[i]?, after.sequences[i]? with
    | some b, some a =>
      if b.final != a.final || b.label != a.label || b.states != a.states then
        out := out ++ s!"edit {i + 1} {a.label}: {sizes b.final a.final}\
          {change "label" b.label a.label}{others b.final a.final}\n"
        for j in [0:max b.states.size a.states.size] do
          match b.states[j]?, a.states[j]? with
          | some sb, some sa =>
            unless sb == sa do out := out ++ s!"  state {j + 1}: {sizes sb sa}{others sb sa}\n"
          | some _, none => out := out ++ s!"  state {j + 1}: only in the recorded results\n"
          | none, some _ => out := out ++ s!"  state {j + 1}: only in the new results\n"
          | none, none => pure ()
      if missed a.final < missed b.final then improved := improved + 1
      else if missed a.final > missed b.final then regressed := regressed + 1
      else sameMissed := sameMissed + 1
    | some b, none => out := out ++ s!"edit {i + 1} {b.label}: only in the recorded results\n"
    | none, some a => out := out ++ s!"edit {i + 1} {a.label}: only in the new results\n"
    | none, none => pure ()
  if before.cold? != after.cold? then
    let lines (c? : Option ColdComparison) : Array String := match c? with
      | some c =>
        (c.onlyWarm.map ("- " ++ ·) ++ c.onlyCold.map ("+ " ++ ·)).map (·.replace "\n" "\n    ")
      | none => #[]
    let (b, a) := (lines before.cold?, lines after.cold?)
    out := out ++ "cold: the cold comparisons differ\n"
    if before.cold?.isNone then out := out ++ "  only the new results have a cold comparison\n"
    if after.cold?.isNone then out := out ++ "  only the recorded results have a cold comparison\n"
    for d in b do unless a.contains d do out := out ++ s!"  only recorded: {d}\n"
    for d in a do unless b.contains d do out := out ++ s!"  only new: {d}\n"
  let reused (r : ReuseReport) := r.sequences.foldl (· + ·.final.result.reused) 0
  return out ++ s!"edit sequences: {improved} improved, {regressed} regressed, \
    {sameMissed} with the same missed reuse; total reused {reused before} → {reused after}\n"

/--
The change in reuse that {name}`reuseChange` describes lists only the edit sequences whose results
differ.
-/
@[test]
def reuseChangeListsDifferences : Test := do
  let reuse (reused : Nat) : EditReuse :=
    { result := { reused, reusable := 1, total := 1, boundarySource := .enclosingBlock },
      errors := 0 }
  let report (second : Nat) : ReuseReport :=
    { baseTotal := 1, baseErrors := 0,
      sequences :=
        #[{ label := "same", final := reuse 0 }, { label := "changed", final := reuse second }] }
  assertBEq "edit 2 changed: reused 0 → 1, reusable 1 → 1\nedit sequences: 1 improved, \
    0 regressed, 1 with the same missed reuse; total reused 0 → 1\n"
    (reuseChange (report 0) (report 1))

/--
Compares a reuse report with the one recorded in a golden file, or records it with
{lit}`--update-golden`. A difference fails with the change in reuse that {name}`reuseChange`
describes and with how to record it.
-/
def reuseGolden (golden : System.FilePath) (report : ReuseReport)
    (loc : Location := by exact here%) : TestM Unit := do
  if (← read).updateGolden then
    if let some dir := golden.parent then IO.FS.createDirAll dir
    IO.FS.writeFile golden report.render
  else if ← golden.pathExists then
    match ReuseReport.parse (← IO.FS.readFile golden), ReuseReport.parse report.render with
    | .error e, _ => failAt loc s!"cannot read the reuse golden {golden}: {e}"
    | _, .error e => failAt loc s!"cannot read the new reuse report: {e}"
    | .ok recorded, .ok new =>
      unless recorded == new do
        failAt loc s!"the reuse differs from {golden}" (detail? := some (reuseChange recorded new ++
          "Once the change is reviewed, record it with --update-golden."))
  else
    failAt loc s!"missing golden file {golden}"
      (detail? := some "Run with --update-golden to create it.")

/--
The language server's reuse after the edits of {name}`reuseCases` matches the golden files in
{name}`serverReuseGoldens`. Each case says what edit it makes and what sizes it expects. A failure
reports the change in reuse.
-/
@[test]
def serverReuse : Test := do
  for (name, input, record) in reuseCases do
    result name do
      let seqs ← IO.ofExcept input
      let doc := scratchDir "." "server-reuse" / s!"{name}.lean"
      let golden := serverReuseGoldens / s!"{name}.txt"
      match record with
      | .reuse opts => reuseGolden golden (← reuseReport "." doc seqs opts)
      | .snapshotTree => goldenFile golden (← snapshotTree "." doc seqs.base)

/--
The language server's reuse after each edit of the benchmark's corpus matches the reuse that the
benchmark recorded in {lit}`bench/reuse/expected`. A failure reports the change in reuse, which is
reviewed whether it is better or worse and then recorded in the benchmark's results.
-/
@[test]
def corpusReuse : Test := do
  for file in ← corpusScripts benchCorpus do
    let name := file.fileStem.getD "script"
    result name do
      let report ← reuseReport "." (scratchDir "." "corpus-reuse" / s!"{name}.lean")
        (← EditSequences.load file)
      reuseGolden (benchResults / s!"{name}.txt") report
