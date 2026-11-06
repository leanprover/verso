/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import VersoUtil.Elan
import Verso
import Verso.Doc.Concrete.BlockOutline
import VersoGen.Server.Basic
import Verso.Doc.Concrete.ReuseMeasure

set_option doc.verso true

/-!
Tests of the block outline and of the trace class `Elab.Verso.blocks`. The block outline reduces
each block syntax node of a top-level block to its kind, range, block size and digest. The trace
messages give the block outline of each top-level block that Verso elaborates. The reuse measure
reads these messages to find what the language server elaborated again after an edit, so its
results are only as good as the outlines. These tests matter when changing the block outline, the
trace or Verso's block parser.

A failure means that the outline of some text lacks the nodes, ranges, block sizes or digests that
the reuse measure relies on, that a trace message doesn't read back into the outline it was made
from, or that the trace messages aren't where the measure expects them.
-/

open Lean Errata Verso.Doc.Concrete.ReuseMeasure

open Verso.Doc.Concrete (BlockOutline BlockElabOutline)

namespace Verso.Tests.VersoGen.BlockOutline

/-- Parses text in Verso's concrete syntax into the syntax of its top-level blocks. -/
def parseBlocks (input : String) : IO (Array Syntax) := do
  let env ← mkEmptyEnvironment
  let ictx := Parser.mkInputContext input "<input>"
  let s := (Verso.Parser.document {}).run ictx { env, options := {} } (Parser.getTokenTable env)
    (Parser.mkParserState input)
  unless s.allErrors.isEmpty do
    throw <| .userError s!"failed to parse: {s.allErrors.map (toString ·.2.2)}"
  return s.stxStack.toSubarray.toArray

/-- The outlines of the top-level blocks of some text in Verso's concrete syntax. -/
def outline (text : String) : IO (Array BlockOutline) := do
  return (← parseBlocks text).flatMap (BlockOutline.ofSyntax (FileMap.ofString text))

def sampleBlocks : String :=
  "Para one.

:::d
Inside.

* a
* b

  ```
  code
  ```
:::

> quote

# Header

: Term

  Text.


After.
"

/--
Block outlines have a node for each block syntax node, with its kind and block size, and block sizes
count list items and description list items as blocks. In {name}`sampleBlocks`, the directive's
list has block size 6: the list, its two items, and the three blocks in them.
-/
@[test]
def blockOutlineShape : Test := do
  let blocks ← outline sampleBlocks
  assertBEq #[1, 8, 2, 1, 3, 1] (blocks.map (·.size))
  assertBEq #[``Lean.Doc.Parser.Block.para, ``Lean.Doc.Parser.Block.directive,
    ``Lean.Doc.Parser.Block.blockquote, ``Lean.Doc.Parser.Block.header, ``Lean.Doc.Parser.Block.dl,
    ``Lean.Doc.Parser.Block.para] (blocks.map (·.kind))
  assertBEq #[1, 6] (blocks[1]!.children.map (·.size))
  let items := blocks[1]!.children[1]!.children
  assertBEq #[``Lean.Doc.Parser.ListItem.item, ``Lean.Doc.Parser.ListItem.item]
    (items.map (·.kind))
  assertBEq #[2, 3] (items.map (·.size))
  assertBEq #[#[1], #[1, 1]] (items.map (·.children.map (·.size)))
  assertBEq #[``Lean.Doc.Parser.DescItem.item] (blocks[4]!.children.map (·.kind))
  assertBEq #[2] (blocks[4]!.children.map (·.size))

/-- Block outlines have nodes of the block syntax kinds that {name}`sampleBlocks` lacks. -/
@[test]
def blockOutlineKinds : Test := do
  let others ← outline "1. One\n\
    2. Two\n\
    \n\
    {separator}\n\
    \n\
    [label]: https://example.com\n\
    \n\
    [^note]: A note.\n\
    \n\
    # Header\n\
    \n\
    %%%\n\
    tag := \"header\"\n\
    %%%\n"
  assertBEq #[``Lean.Doc.Parser.Block.ol, ``Lean.Doc.Parser.Block.command,
    ``Lean.Doc.Parser.Block.link_ref, ``Lean.Doc.Parser.Block.footnote_ref,
    ``Lean.Doc.Parser.Block.header, ``Lean.Doc.Parser.Block.metadata_block]
    (others.map (·.kind))
  assertBEq #[``Lean.Doc.Parser.ListItem.item, ``Lean.Doc.Parser.ListItem.item]
    (others[0]!.children.map (·.kind))

/--
Summarizes a block outline, one line per block syntax node in document order, indented two spaces
per level, starting at {name}`indent`. Each line gives the node's kind, the line and column of the
start and end of its range and its block size. Every line ends with a line break.
-/
partial def summarize (b : BlockOutline) (indent : Nat) : String :=
  let range := match b.range? with
    | some r =>
      let lineColumn (p : Position) := s!"{p.line}:{p.column}"
      s!"{lineColumn r.startPosition}-{lineColumn r.stopPosition}"
    | none => "?"
  let line := "".pushn ' ' indent ++ s!"{b.kind.getString!} {range} size {b.size}\n"
  b.children.foldl (init := line) fun out c => out ++ summarize c (indent + 2)

/-- A trace message of {lit}`Elab.Verso.blocks` with a block outline. -/
def traceMessage (blocks : Array BlockOutline) (elaborated : String := "") : String :=
  tracePrefix ++ (toJson ({ elaborated, blocks } : BlockElabOutline)).pretty

/--
Block outlines give each block syntax node's range and the digest of its source text. Ranges end at
the node's last token: the description list in {name}`sampleBlocks` ends at 20:7, before the blank
lines that follow it.
-/
@[test]
def blockOutlineRanges : Test := do
  let outline ← outline sampleBlocks
  -- The last paragraph ends before the line break at the end of the text, at 23:6.
  assertBEq "para 1:0-1:9 size 1
directive 3:0-12:3 size 8
  para 4:0-4:7 size 1
  ul 6:0-11:5 size 6
    item 6:0-6:3 size 2
      para 6:2-6:3 size 1
    item 7:0-11:5 size 3
      para 7:2-7:3 size 1
      codeblock 9:2-11:5 size 1
blockquote 14:0-14:7 size 2
  para 14:2-14:7 size 1
header 16:0-16:8 size 1
dl 18:0-20:7 size 3
  item 18:0-20:7 size 2
    para 20:2-20:7 size 1
para 23:0-23:6 size 1
"
    (outline.foldl (init := "") fun out b => out ++ summarize b 0)
  for b in outline.flatMap BlockOutline.flatten do
    let source := sampleBlocks.slice! (sampleBlocks.pos! b.startPos) (sampleBlocks.pos! b.stopPos)
    assertBEq (BlockOutline.digestOf source) b.digest

/--
Trace messages of block outlines read back into the same outlines, also when nodes without a range
are at the top level, parents or nested children.
-/
@[test]
def blocksTraceRoundTrip : Test := do
  let outline ← outline sampleBlocks
  result "outline of sampleBlocks" do
    assertBEq outline (parseBlocksTrace (traceMessage outline "1990-01-01 00:00:00.000000"))
  result "nodes without a range" do
    let paras := outline.flatMap BlockOutline.flatten
      |>.filter (·.kind == ``Lean.Doc.Parser.Block.para)
    let noRange (size : Nat) (children : Array BlockOutline := #[]) : BlockOutline :=
      { kind := ``Lean.Doc.Parser.Block.ul, range? := none, size, digest := "0", hasMissing := true,
        children }
    let mixed := #[noRange 3 #[paras[0]!, paras[1]!], paras[2]!, noRange 2 #[noRange 1]]
    assertBEq mixed (parseBlocksTrace (traceMessage mixed))

/--
Trace messages that differ only in the time at which their block was elaborated are equal after
{name}`stripElaborationTime`.
-/
@[test]
def stripElaborationTimeIgnoresTime : Test := do
  let outline ← outline sampleBlocks
  assertBEq (stripElaborationTime (traceMessage outline "1990-01-01 00:00:00.000000"))
    (stripElaborationTime (traceMessage outline "1990-01-01 00:00:01.000000 UTC"))

/--
Elaborates a document with {lit}`lake lean` and the trace class {lit}`Elab.Verso.blocks` enabled and
returns the process's output and its messages as JSON. {name}`body` is the document's text after its
{lit}`#doc` line. The document is written to {lit}`Doc.lean` in the scratch directory whose name is
{name}`dir`.
-/
def elabWithBlocksTrace (dir body : String) : IO (IO.Process.Output × Array Json) := do
  let dir := VersoGen.Server.scratchDir "." dir
  IO.FS.createDirAll dir
  let file := dir / "Doc.lean"
  IO.FS.writeFile file (r#"import Verso
set_option trace.Elab.Verso.blocks true
#doc (.none) "T" =>
"# ++ body)
  let out ← IO.Process.output <|
    Verso.Elan.getSpawnArgsForLake #["lean", file.toString, "--", "--json"]
  let mut messages := #[]
  for line in out.stdout.split '\n' do
    unless line.isEmpty do messages := messages.push (← IO.ofExcept (Json.parse line.copy))
  return (out, messages)

/--
The trace messages of `Elab.Verso.blocks` are at the first lines of their top-level blocks. Their
records say whether each top-level block's syntax contains {lit}`.missing`, also when the recovery
of the {lit}`#doc` command places it beside the block's nodes, as after the role without contents in
the third block.
-/
@[test]
def blocksTraceMessages : Test := do
  let (out, messages) ← elabWithBlocksTrace "blocks-trace" "
One.

* a
* b

a {r x}

Two.
"
  let line (m : Json) : Option Nat :=
    (m.getObjVal? "pos").toOption.bind fun p => (p.getObjValAs? Nat "line").toOption
  let detail := some (out.stdout ++ out.stderr)
  let traces := messages.filterMap fun m =>
    let data := (m.getObjValAs? String "data").toOption.getD ""
    if data.startsWith tracePrefix then some (m, data) else none
  unless traces.size == 4 do
    fail s!"elaboration gave {traces.size} trace messages instead of 4" (detail? := detail)
  let records := traces.filterMap (blockElabOutline? ·.2)
  unless records.size == traces.size do
    fail "a trace message isn't a block outline" (detail? := detail)
  result "positions" do
    assertBEq #[5, 7, 10, 12] (traces.filterMap (line ·.1))
  result "missing" do
    assertBEq #[false, false, true, false] (records.map (·.hasMissing))
    for record in records do
      for b in record.blocks.flatMap BlockOutline.flatten do
        assertTrue (!b.hasMissing) "no node of the outlines has `.missing`"

/--
Parses one top-level block with the error recovery of the {lit}`#doc` command, which keeps the
partial syntax of a block that fails to parse. Returns the syntax and the number of parse errors.
-/
def parseRecoveredBlock (input : String) : IO (Syntax × Nat) := do
  let env ← mkEmptyEnvironment
  let ictx := Parser.mkInputContext input "<input>"
  let s := Verso.Parser.blockCommandRecovery.run ictx
    { env, options := {} } (Parser.getTokenTable env) (Parser.mkParserState input)
  return (s.stxStack.back, s.allErrors.size)

/--
Block outlines of blocks that failed to parse have a node with the right kind for each block syntax
node of the partial syntax, and each node records whether its own syntax contains {lit}`.missing`.
Their ranges lie within the text and end before line breaks, even when the last token is a code line
that ends with one.
-/
@[test]
def recoveredBlockOutline : Test := do
  let directive := ``Lean.Doc.Parser.Block.directive
  let para := ``Lean.Doc.Parser.Block.para
  let cases : List (String × String × Array (Name × Bool)) := [
    ("unclosed emphasis", "Some *unclosed emphasis\n", #[(para, true)]),
    ("unclosed directive", ":::d\nInside.\n", #[(directive, true), (para, false)]),
    ("unclosed code block", "```\ncode\n", #[(``Lean.Doc.Parser.Block.codeblock, true)]),
    ("stray bracket", "]\n", #[(para, true)]),
    ("unclosed directive in a list item", "* :::d\n  Inside.\n",
      #[(``Lean.Doc.Parser.Block.ul, true), (``Lean.Doc.Parser.ListItem.item, true),
        (directive, true), (para, false)]),
    ("unclosed directive in a description list item", ": Term\n\n  :::d\n  Inside.\n",
      #[(``Lean.Doc.Parser.Block.dl, true), (``Lean.Doc.Parser.DescItem.item, true),
        (directive, true), (para, false)]),
    ("complete directive", ":::d\nInside.\n:::\n", #[(directive, false), (para, false)])
  ]
  for (name, text, nodes) in cases do
    result name do
      let (stx, errors) ← parseRecoveredBlock text
      let complete := nodes.all (!·.2)
      assertTrue (complete == (errors == 0)) "a parse error unless the block is complete"
      assertTrue (complete == !stx.hasMissing) "`.missing` unless the block is complete"
      let fileMap := FileMap.ofString text
      let outline := BlockOutline.ofSyntax fileMap stx
      assertBEq nodes (outline.flatMap BlockOutline.flatten |>.map fun b => (b.kind, b.hasMissing))
      for b in outline.flatMap BlockOutline.flatten do
        assertTrue (b.stopPos ≤ text.rawEndPos) "the range lies within the text"
        assertTrue (!(text.slice! (text.pos! b.startPos) (text.pos! b.stopPos)).endsWith "\n")
          "the range ends before a line break"
      assertBEq outline (parseBlocksTrace (traceMessage outline))

/--
Block outlines of {lit}`.missing` are empty, and the outline of a null node that groups partial
blocks and {lit}`.missing`, as the recovery of the {lit}`#doc` command can make, consists of the
outlines of the blocks.
-/
@[test]
def recoveredGroupOutline : Test := do
  assertBEq #[] (BlockOutline.ofSyntax (FileMap.ofString "") .missing)
  let text := "Some *unclosed emphasis\n"
  let (para, _) ← parseRecoveredBlock text
  let group := mkNullNode #[para, para, .missing]
  let fileMap := FileMap.ofString text
  assertBEq (BlockOutline.ofSyntax fileMap para ++ BlockOutline.ofSyntax fileMap para)
    (BlockOutline.ofSyntax fileMap group)
  assertBEq (BlockOutline.blockTextRange? para) (BlockOutline.blockTextRange? group)

/--
When the recovery of the {lit}`#doc` command places {lit}`.missing` beside a block syntax node
instead of inside it, the top-level block's syntax contains {lit}`.missing` but no node of the
outline does. Roles without contents, such as {lit}`{r x}` at the end of a line, are recovered this
way.
-/
@[test]
def recoveredBlockBesideMissing : Test := do
  for (name, text) in [("paragraph", "a {r x}\n"), ("list", "* a {r x}\n* b\n"),
      ("directive", ":::d\na {r x}\n:::\n"), ("blockquote", "> a {r x}\n"),
      ("header", "# H {r x}\n")] do
    result name do
      let (stx, errors) ← parseRecoveredBlock text
      assertTrue (errors > 0) "a parse error"
      assertTrue stx.hasMissing "the syntax has `.missing`"
      let outline := BlockOutline.ofSyntax (FileMap.ofString text) stx
      assertTrue (!outline.isEmpty) "an outline"
      for b in outline.flatMap BlockOutline.flatten do
        assertTrue (!b.hasMissing) "no node of the outline has `.missing`"
