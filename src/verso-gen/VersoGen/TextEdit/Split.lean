/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.TextEdit.Basic
public import Plausible.Gen

set_option doc.verso true

/-!
The splitting strategies, which turn the replacements between two texts into a sequence of smaller
replacements, as an editor would send them.
-/

namespace VersoGen.TextEdit

open Lean

/-- How the replacements between two texts become a sequence of edits. -/
public inductive SplitStrategy where
  /-- One edit for each replacement, like a paste or a quick edit. -/
  | wholeHunks
  /--
  Each replacement's old text is deleted, and its new text is typed a few characters at a time.
  -/
  | typing
  /--
  A short piece of nonsense is inserted where each replacement goes, the replacement is made after
  it, and the nonsense is then removed.
  -/
  | garbage
deriving ToJson, FromJson, BEq, Repr, Inhabited

/-- Short pieces of nonsense that break Verso syntax. -/
public def garbagePieces : List String := [":::", "```", "{", "[^", "*_", "%%%", "](", "\n# "]

/--
Splits the replacements between two texts into a sequence of replacements, with the strategy's
random choices drawn in {name}`Plausible.Gen`. The given replacements are in document order, with
positions in the first text. Each replacement of the result has positions in the text that the
replacements before it give.
-/
public def splitReplacements (strategy : SplitStrategy) (reps : Array Replacement) :
    Plausible.Gen (Array Replacement) := do
  let mut out : Array Replacement := #[]
  -- The end of the previous replacement, in the first text and in the current text
  let mut oldCursor : String.Pos.Raw := 0
  let mut cursor : String.Pos.Raw := 0
  for r in reps do
    let start := (r.start.unoffsetBy oldCursor).offsetBy cursor
    let stop := (r.stop.unoffsetBy r.start).offsetBy start
    match strategy with
    | .wholeHunks => out := out.push { start, stop, text := r.text }
    | .typing =>
      if stop > start then out := out.push { start, stop, text := "" }
      let mut pos := start
      let mut chunkStart : String.Pos.Raw := 0
      while chunkStart < r.text.rawEndPos do
        let n := (← Plausible.Gen.choose Nat 1 4 (by decide)).val
        let chunkStop := n.fold (init := chunkStart) fun _ _ p =>
          if p < r.text.rawEndPos then p.next r.text else p
        let chunk := String.Pos.Raw.extract r.text chunkStart chunkStop
        chunkStart := chunkStop
        out := out.push { start := pos, stop := pos, text := chunk }
        pos := pos + chunk
    | .garbage =>
      let piece ← Plausible.Gen.elements garbagePieces (by decide)
      out := out.push { start, stop := start, text := piece }
      out := out.push { start := start + piece, stop := stop + piece, text := r.text }
      out := out.push { start, stop := start + piece, text := "" }
    oldCursor := r.stop
    cursor := start + r.text
  return out
