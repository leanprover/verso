/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Util.Diff
public import Lean.Data.Lsp.Basic
public import Lean.Data.Lsp.Utf16
public import Lean.Server.Utils

set_option doc.verso true

/-!
Replacements of ranges of a text with new text, the replacements that turn one text into another,
and their conversion to LSP edits. The texts are compared with {name}`Lean.Diff.diff`, first by
lines and then by characters within the changed lines.
-/

namespace VersoGen.TextEdit

open Lean

/--
A replacement of the text from one position up to another with a new text. The positions are byte
positions in the text that the replacement applies to, at the boundaries of characters.
-/
public structure Replacement where
  /-- The position of the first replaced character. -/
  start : String.Pos.Raw
  /-- The position after the last replaced character. -/
  stop : String.Pos.Raw
  text : String
deriving BEq, Repr, Inhabited

/--
The text that a replacement gives in {name}`s`: the text before the replacement's start, its new
text, and the text after its stop. The result is {name}`none` when the start or the stop isn't a
valid position of {name}`s`, or when the stop is before the start.
-/
public def Replacement.apply? (r : Replacement) (s : String) : Option String :=
  if h : r.start.IsValid s ∧ r.stop.IsValid s ∧ r.start ≤ r.stop then
    some (s.extract s.startPos (s.pos r.start h.1) ++ r.text ++
      s.extract (s.pos r.stop h.2.1) s.endPos)
  else none

/-- Replacements apply exactly when their positions are valid and in order. -/
public theorem Replacement.apply?_eq_some_iff {r : Replacement} {s t : String} :
    r.apply? s = some t ↔ ∃ (hstart : r.start.IsValid s) (hstop : r.stop.IsValid s),
      r.start ≤ r.stop ∧ t = s.extract s.startPos (s.pos r.start hstart) ++ r.text ++
        s.extract (s.pos r.stop hstop) s.endPos := by
  rw [apply?]
  split <;> grind

/--
Applies replacements in order, each to the text that the ones before it give. The result is
{name}`none` when one of them doesn't apply.
-/
public def applyAll? (text : String) (reps : List Replacement) : Option String :=
  reps.foldlM (fun text r => r.apply? text) text

/-- Applying replacements applies the first one and then the rest to the text that it gives. -/
public theorem applyAll?_cons {text : String} {r : Replacement} {rs : List Replacement} :
    applyAll? text (r :: rs) = (r.apply? text).bind (applyAll? · rs) := by
  simp only [applyAll?, List.foldlM_cons]
  rfl

/--
The LSP edits of a sequence of replacements. Each replacement's positions are positions in the text
that the replacements before it give, starting from {name}`text`.
-/
public def toLspEdits (text : String) (reps : Array Replacement) : Array Lsp.TextEdit :=
  (reps.foldl (init := (text, #[])) fun (text, edits) r =>
    let fileMap := FileMap.ofString text
    let range : Lsp.Range := ⟨fileMap.utf8PosToLspPos r.start, fileMap.utf8PosToLspPos r.stop⟩
    ((r.apply? text).getD text, edits.push { range, newText := r.text })).2

/--
Merges replacements that are separated by fewer than {name}`gap` unchanged characters of
{name}`old`.
-/
def mergeClose (old : String) (gap : Nat) (reps : Array Replacement) :
    Array Replacement := Id.run do
  let mut out : Array Replacement := #[]
  for r in reps do
    match out.back? with
    | some prev =>
      let between := old.slice! (old.pos! prev.stop) (old.pos! r.start)
      if between.positions.length < gap then
        out := out.pop.push { prev with stop := r.stop, text := prev.text ++ between ++ r.text }
      else out := out.push r
    | none => out := out.push r
  return out

/--
The character-level replacements that turn {name}`old` into {name}`new`, with offsets from
{name}`base`.
-/
def charDiff (base : String.Pos.Raw) (old new : String) : Array Replacement := Id.run do
  let d := Diff.diff (old.foldl Array.push #[]) (new.foldl Array.push #[])
  let mut out : Array Replacement := #[]
  let mut pos := base
  let mut cur : Option Replacement := none
  for (act, c) in d do
    match act with
    | .skip =>
      if let some r := cur then out := out.push r
      cur := none
      pos := pos + c
    | .delete =>
      let r := cur.getD { start := pos, stop := pos, text := "" }
      cur := some { r with stop := r.stop + c }
      pos := pos + c
    | .insert =>
      let r := cur.getD { start := pos, stop := pos, text := "" }
      cur := some { r with text := r.text.push c }
  if let some r := cur then out := out.push r
  return out

/--
The replacements that turn {name}`old` into {name}`new`, in document order. Lines are compared
first and then the characters of each sequence of changed lines. Replacements that are separated
by fewer than four unchanged characters are merged.
-/
public def textDiff (old new : String) : Array Replacement := Id.run do
  -- The lines of both texts, each with its line terminator
  let d := Diff.diff (old.splitInclusive '\n').toArray (new.splitInclusive '\n').toArray
  let mut out : Array Replacement := #[]
  let mut pos : String.Pos.Raw := 0
  let mut hunk : Option (String.Pos.Raw × String × String) := none
  for (act, l) in d do
    match act with
    | .skip =>
      if let some (start, o, n) := hunk then out := out ++ charDiff start o n
      hunk := none
      pos := pos + l
    | .delete =>
      let (start, o, n) := hunk.getD (pos, "", "")
      hunk := some (start, o ++ l, n)
      pos := pos + l
    | .insert =>
      let (start, o, n) := hunk.getD (pos, "", "")
      hunk := some (start, o, n ++ l)
  if let some (start, o, n) := hunk then out := out ++ charDiff start o n
  return mergeClose old 4 out

public def applyTextEdit (s : String) (e : Lsp.TextEdit) : String :=
  (Server.replaceLspRange (FileMap.ofString s) e.range e.newText).source
