/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Position
public import Verso.Doc.Concrete.BlockOutline

set_option doc.verso true

/-!
A measure of how much of a Verso document the language server reuses after an edit, for the language
server tests and the benchmarks. It reads the block outlines that the trace class
`Elab.Verso.blocks` reports and the {lit}`reuse stopped` messages of {option}`trace.Elab.reuse`, and
computes the reused size and the reusable size.

The block size of a block syntax node is the number of block syntax nodes in its syntax, including
itself. List items and description list items count as blocks. Reuse is prefix-based at every
level. The reused size is the total size of the largest block syntax nodes that end at or before
the reuse boundary. The reusable size is the total size of the largest block syntax nodes that the
edit leaves unchanged.
-/

namespace Verso.Doc.Concrete.ReuseMeasure

open Lean

open Verso.Doc.Concrete (BlockOutline BlockElabOutline)

/-- The prefix of an `Elab.Verso.blocks` trace message. -/
public def tracePrefix : String := "[Elab.Verso.blocks] "

/--
The {name}`BlockElabOutline` that the text of an `Elab.Verso.blocks` trace message gives, or
{name}`none` for any other message.
-/
public def blockElabOutline? (msg : String) : Option BlockElabOutline := do
  let value ← msg.dropPrefix? tracePrefix
  (Json.parse value.copy >>= fromJson?).toOption

/--
Removes the time at which a block was elaborated from the text of an `Elab.Verso.blocks` trace
message. Other messages are unchanged.
-/
public def stripElaborationTime (msg : String) : String :=
  match blockElabOutline? msg with
  | some trace => tracePrefix ++ (toJson { trace with elaborated := "" }).pretty
  | none => msg

/--
The outlines of the outermost block syntax nodes that an `Elab.Verso.blocks` trace message reports,
or none for any other message.
-/
public def parseBlocksTrace (msg : String) : Array BlockOutline :=
  (blockElabOutline? msg).map (·.blocks) |>.getD #[]

/-- The total size of block syntax nodes. -/
public def totalSize (blocks : Array BlockOutline) : Nat := blocks.foldl (· + ·.size) 0

/-- The total size of the largest block syntax nodes that end at or before a position. -/
partial def reusedSize (blocks : Array BlockOutline) (boundary : String.Pos.Raw) : Nat :=
  blocks.foldl (init := 0) fun acc b =>
    if b.stopPos ≤ boundary then acc + b.size
    else acc + reusedSize b.children boundary

/--
The total size of the largest block syntax nodes that an edit from {name}`editPos` leaves unchanged.
Block syntax nodes are unchanged if they end before {name}`editPos`, or if they end at
{name}`editPos` and a block syntax node in {name}`after` has the same range, size and digest.

The command of the document's last top-level block is of another kind than the commands of the other
blocks, because it finishes the document. Text added after the last block gives it the kind of the
other blocks' commands, so the server elaborates it again. The block syntax nodes that end where the
last top-level block ends, at {name}`lastStop`, are unchanged only if the edit is before them.
-/
partial def reusableSize (blocks : Array BlockOutline) (editPos : String.Pos.Raw)
    (after : Array BlockOutline) (lastStop : Option String.Pos.Raw := none) : Nat :=
  let same (b : BlockOutline) := after.any fun a =>
    a.startPos == b.startPos && a.stopPos == b.stopPos && a.size == b.size && a.digest == b.digest
  let atEnd (b : BlockOutline) := lastStop == some b.stopPos
  blocks.foldl (init := 0) fun acc b =>
    if !atEnd b && (b.stopPos < editPos || (b.stopPos == editPos && same b)) then acc + b.size
    else acc + reusableSize b.children editPos after lastStop

/-- Where a reuse boundary came from. -/
public inductive BoundarySource where
  /-- A {lit}`reuse stopped` message of {option}`trace.Elab.reuse`. -/
  | reuseStopped
  /-- The start of the top-level block that contains the edit. -/
  | enclosingBlock
deriving Repr, BEq, Inhabited

/-- The reuse after an edit. -/
public structure ReuseResult where
  reused : Nat
  reusable : Nat
  total : Nat
  boundarySource : BoundarySource
deriving Repr, BEq, Inhabited

/--
Measures reuse. {name}`blocks` are the top-level block syntax nodes before the edit, {name}`editPos`
is the first byte that the edit changed, and {name}`after` are the top-level block syntax nodes
after the edit. Positions before the edit are the same in both texts. {name}`stops` are the
positions of all {lit}`reuse stopped` messages after the edit, and {name}`newStops` are the
positions of the messages that are new since before the edit.

The reuse boundary is the first of these that applies:
* If a new message is at or before the edit, the latest message at or before the edit.
* If a new message is after the edit, the earliest new message. An edit in the whitespace after a
  block leads to this case.
* If any message is after the edit, the earliest one.
* If any message is at or before the edit, the latest one.
* The start of the top-level block that contains the edit, or the start of the document if the edit
  is before the first block.
-/
public def measure (blocks : Array BlockOutline) (editPos : String.Pos.Raw)
    (stops : Array String.Pos.Raw) (after : Array BlockOutline := #[])
    (newStops : Array String.Pos.Raw := stops) : ReuseResult :=
  let stops := stops ++ newStops
  let atOrBefore := stops.filter (· ≤ editPos)
  let later := stops.filter (· > editPos)
  let newLater := newStops.filter (· > editPos)
  let fallback : String.Pos.Raw := (blocks.map (·.startPos) |>.filter (· ≤ editPos)).max?.getD 0
  let (boundary, source) : String.Pos.Raw × BoundarySource :=
    if newStops.any (· ≤ editPos) then (atOrBefore.max?.getD fallback, .reuseStopped)
    else match newLater.min?, later.min?, atOrBefore.max? with
      | some b, _, _ | none, some b, _ | none, none, some b => (b, .reuseStopped)
      | none, none, none => (fallback, .enclosingBlock)
  let after := after.flatMap BlockOutline.flatten
  let last : Option BlockOutline := blocks.foldl (init := none) fun last b =>
    if last.all (fun l => l.startPos ≤ b.startPos) then some b else last
  let lastStop := last.map (·.stopPos)
  { reused := reusedSize blocks boundary, reusable := reusableSize blocks editPos after lastStop,
    total := totalSize blocks, boundarySource := source }

/-- A size as a percentage of a total, with one decimal. -/
public def percent (part whole : Nat) : String :=
  if whole == 0 then "-" else
  let tenths := (part * 1000 + whole / 2) / whole
  s!"{tenths / 10}.{tenths % 10}%"

/-- Describes where a reuse boundary came from, in the words of reuse reports. -/
public def BoundarySource.describe : BoundarySource → String
  | .reuseStopped => "reuse stopped"
  | .enclosingBlock => "enclosing block"

/-- Describes a reuse result on one line. -/
public def ReuseResult.describe (r : ReuseResult) : String :=
  s!"reused {r.reused} ({percent r.reused r.total}) reusable {r.reusable} \
    ({percent r.reusable r.total}) total {r.total} boundary {r.boundarySource.describe}"
