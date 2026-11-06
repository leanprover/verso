/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Json.FromToJson
public import Lean.Data.Position
public import Lean.DocString.Syntax
public import Std.Time.Zoned
public import Std.Time.Format

set_option doc.verso true

/-!
The block outline of a top-level block, which the trace class `Elab.Verso.blocks` reports as JSON
for each top-level block of a `#doc` document. The outline describes the block syntax nodes of the
block, nested as the nodes are, with enough about each one to tell whether an edit left it
unchanged. The language server tests and the reuse measure read the trace to see which blocks were
elaborated again after an edit.
-/

namespace Verso.Doc.Concrete

open Lean

/--
The source range of a block syntax node's text, as byte positions and as lines and columns. Programs
that read the trace use the byte positions. The lines and columns are for people.
-/
public structure BlockRange where
  /-- The position of the node's first character. -/
  start : String.Pos.Raw
  /-- The position after the node's last character. -/
  stop : String.Pos.Raw
  /-- The line and column of {name}`BlockRange.start`. -/
  startPosition : Position
  /-- The line and column of {name}`BlockRange.stop`. -/
  stopPosition : Position
deriving Inhabited, Repr, BEq

public instance : ToJson BlockRange where
  toJson r := Json.mkObj [
    ("start", r.start.byteIdx), ("stop", r.stop.byteIdx),
    ("startPosition", toJson r.startPosition), ("stopPosition", toJson r.stopPosition)
  ]

public instance : FromJson BlockRange where
  fromJson? j := do
    return {
      start := ⟨← j.getObjValAs? Nat "start"⟩, stop := ⟨← j.getObjValAs? Nat "stop"⟩,
      startPosition := ← j.getObjValAs? Position "startPosition",
      stopPosition := ← j.getObjValAs? Position "stopPosition"
    }

namespace BlockOutline

/--
The range of a block syntax node's text, from its first token to its last. Tokens without positions,
empty tokens and line break nodes are left out. Tokens' ranges end before the line breaks at their
ends. The range therefore ends before any line break that ends the node.
-/
public partial def blockTextRange? : Syntax → Option Syntax.Range
  | .atom info val => do
    let start ← info.getPos?
    let stop := min (← info.getTailPos?) (start + val.dropEndWhile '\n')
    let r : Syntax.Range := ⟨start, stop⟩
    if r.start < r.stop then some r else none
  | .ident info .. => do
    let r : Syntax.Range := ⟨← info.getPos?, ← info.getTailPos?⟩
    if r.start < r.stop then some r else none
  | .node _ k args =>
    if k == ``Lean.Doc.Parser.Inline.linebreak then none
    else args.foldl (init := none) fun acc a =>
      match acc, blockTextRange? a with
      | some r, some r' => some ⟨min r.start r'.start, max r.stop r'.stop⟩
      | r, none | none, r => r
  | .missing => none

/-- A digest of a block syntax node's source text, as 16 hexadecimal digits. -/
public def digestOf (text : String.Slice) : String := (hash text).toBitVec.toHex

/--
Whether a syntax kind is the kind of a block syntax node: a block, a list item or a description
list item.

The block syntax kinds are those in the namespace `Lean.Doc.Parser.Block`.
-/
public def isBlockKind (k : SyntaxNodeKind) : Bool :=
  k.getPrefix == `Lean.Doc.Parser.Block ||
    k == ``Lean.Doc.Parser.ListItem.item || k == ``Lean.Doc.Parser.DescItem.item

end BlockOutline

/--
The outline of a block syntax node: its kind, source range, block size, digest, whether it contains
{name}`Syntax.missing`, and the outlines of the outermost block syntax nodes in it.
-/
public structure BlockOutline where
  /-- The node's syntax kind. -/
  kind : SyntaxNodeKind
  /--
  The range of the node's text, as {name}`BlockOutline.blockTextRange?` gives it. A node of partial
  syntax whose tokens have no positions has none.
  -/
  range? : Option BlockRange
  /--
  The node's block size: the number of block syntax nodes in its syntax, including itself. List
  items and description list items count as blocks.
  -/
  size : Nat
  /-- The digest of the node's source text, as {name}`BlockOutline.digestOf` gives it. -/
  digest : String
  /-- Whether the node's syntax contains {name}`Syntax.missing`. -/
  hasMissing : Bool
  /-- The outlines of the outermost block syntax nodes in the node. -/
  children : Array BlockOutline := #[]
deriving Inhabited, Repr, BEq, ToJson, FromJson

namespace BlockOutline

/--
The outermost block syntax nodes in some syntax. {name}`text` is the source text of the syntax.

A block syntax node is syntax whose kind satisfies {name}`isBlockKind`. The children of its outline
are the outlines of the outermost block syntax nodes in its arguments. Complete blocks and the
partial syntax of a block that the parser left unfinished are outlined alike. Other syntax, such as
the null node that groups partial block syntax in recovered syntax, has the outlines of the block
syntax nodes inside it.
-/
public partial def ofSyntax (text : FileMap) (stx : Syntax) : Array BlockOutline :=
  let children := stx.getArgs.flatMap (ofSyntax text)
  if isBlockKind stx.getKind then #[node stx children] else children
where
  /--
  The outline of a block syntax node, given the outlines of the outermost block syntax nodes in it.
  -/
  node (stx : Syntax) (children : Array BlockOutline) : BlockOutline :=
    let range? := blockTextRange? stx |>.map fun r => {
      start := r.start, stop := r.stop,
      startPosition := text.toPosition r.start, stopPosition := text.toPosition r.stop
    }
    let source := match range? with
      | some r => String.Pos.Raw.extract text.source r.start r.stop
      | none => ""
    { kind := stx.getKind, range?, size := 1 + children.foldl (· + ·.size) 0,
      digest := digestOf source, hasMissing := stx.hasMissing, children }

/-- The position of the node's first character, or 0 if it has no range. -/
public def startPos (b : BlockOutline) : String.Pos.Raw := (b.range?.map (·.start)).getD 0

/-- The position after the node's last character, or 0 if it has no range. -/
public def stopPos (b : BlockOutline) : String.Pos.Raw := (b.range?.map (·.stop)).getD 0

/-- The node and all the block syntax nodes in it, in document order. -/
public partial def flatten (b : BlockOutline) : Array BlockOutline :=
  #[b] ++ b.children.flatMap flatten

end BlockOutline

/-!
# The Trace Message
-/

/--
The time at which a top-level block was elaborated, whether its syntax contains
{name}`Syntax.missing`, and the block outline of its syntax. The trace class `Elab.Verso.blocks`
reports it as JSON.
-/
public structure BlockElabOutline where
  /--
  The date and time at which the block was elaborated, to the microsecond, in local time. When the
  local time zone is unknown, the time is in UTC and ends with ` UTC`.
  -/
  elaborated : String
  /--
  Whether the syntax of the top-level block contains {name}`Syntax.missing`. The error recovery of
  the `#doc` command can place {name}`Syntax.missing` beside a block syntax node, outside every
  node of the outline.
  -/
  hasMissing : Bool := false
  /-- The outlines of the outermost block syntax nodes in the top-level block's syntax. -/
  blocks : Array BlockOutline
deriving Inhabited, Repr, BEq, ToJson, FromJson

/--
The current date and time, to the microsecond, in local time. When the local time zone can't be
found, it is the time in UTC followed by ` UTC`.
-/
def elaborationTime : IO String := do
  let format := "uuuu-MM-dd HH:mm:ss.SSSSSS"
  try
    return (← Std.Time.PlainDateTime.now).format format
  catch _ =>
    let now ← Std.Time.Timestamp.now
    let time := Std.Time.PlainDateTime.ofWallTime (Std.Time.WallTime.ofTimestamp now .zero)
    return time.format format ++ " UTC"

/--
The text of the `Elab.Verso.blocks` message for a top-level block: a pretty-printed JSON value that
gives the time at which the block is elaborated, whether its syntax contains
{name}`Syntax.missing`, and the block outline of its syntax. {name}`text` is the source text of the
syntax.
-/
public def BlockOutline.describeElaborated (text : FileMap) (stx : Syntax) : IO String := do
  let trace : BlockElabOutline := {
    elaborated := ← elaborationTime, hasMissing := stx.hasMissing,
    blocks := BlockOutline.ofSyntax text stx
  }
  return (toJson trace).pretty
