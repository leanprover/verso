/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.Server.Basic
public import VersoGen.Edit.Script
public import Verso.Doc.Concrete.ReuseMeasure

set_option doc.verso true

/-!
The language server's reuse, measured over a session that replays edit sequences. The server runs
with {option}`trace.Elab.reuse` and the trace class `Elab.Verso.blocks`, and the reuse measure reads
its messages. The reused size comes only from the server's {lit}`reuse stopped` messages and from
which `Elab.Verso.blocks` messages are new, so each result is evidence of what the server reused.
-/

namespace VersoGen.Server

open Lean Lean.Lsp

open VersoGen.Edit VersoGen.TextEdit Verso.Doc.Concrete.ReuseMeasure

open Verso.Doc.Concrete (BlockOutline)

/-- Whether a diagnostic is a {lit}`reuse stopped` message of {option}`trace.Elab.reuse`. -/
def isReuseStopped (d : TextDiagnostic) : Bool := d.text.startsWith "reuse stopped"

/-- Whether a diagnostic is a message of {option}`trace.Elab.Verso.blocks`. -/
def isBlocksTrace (d : TextDiagnostic) : Bool := d.text.startsWith tracePrefix

/-- The block outlines of the top-level blocks that diagnostics describe, in document order. -/
def blockOutlines (diags : Array TextDiagnostic) : Array BlockOutline :=
  diags.filter isBlocksTrace
    |>.flatMap (parseBlocksTrace ·.text) |>.qsort (·.startPos < ·.startPos)

/--
Whether the {lit}`reuse stopped` message {name}`d` in {name}`diags`, at {name}`pos`, is new since
{name}`prev`.

{lit}`reuse stopped` messages at the start of a top-level block are new when the
`Elab.Verso.blocks` message that describes that block is new. That message gives the time at which
the block was elaborated. Other {lit}`reuse stopped` messages, such as those of the header's
commands, are new when no message in {name}`prev` has the same text at the same position.
-/
public def isNew (prev diags : Array TextDiagnostic) (d : TextDiagnostic) (pos : String.Pos.Raw) :
    Bool :=
  let traces := diags.filter fun t =>
    isBlocksTrace t && (parseBlocksTrace t.text).any (·.startPos == pos)
  if traces.isEmpty then !prev.contains d else traces.any (!prev.contains ·)

public structure ReuseOptions where
  /-- Report after each LSP edit, not only after each edit sequence. -/
  each : Bool := false
  /-- At the end, compare the session's diagnostics with those of a cold elaboration. -/
  cold : Bool := false

/-- The reuse after an edit sequence or one of its LSP edits, with the number of errors. -/
public structure EditReuse where
  result : ReuseResult
  errors : Nat
deriving BEq, Repr, Inhabited

/-- The reuse after one edit sequence of a session. -/
public structure SequenceReuse where
  label : String
  /--
  The reuse after each LSP edit of the sequence, which is measured only with
  {name}`ReuseOptions.each`.
  -/
  states : Array EditReuse := #[]
  /-- The reuse after the whole sequence. -/
  final : EditReuse
deriving BEq, Repr, Inhabited

/--
The result of a cold comparison: the diagnostics that differ, as {name}`TextDiagnostic.describe`
describes them.
-/
public structure ColdComparison where
  /-- The session's diagnostics that the cold elaboration lacks. -/
  onlyWarm : Array String := #[]
  /-- The diagnostics of the cold elaboration that the session lacks. -/
  onlyCold : Array String := #[]
deriving BEq, Repr, Inhabited

/--
The cold comparison of the session's diagnostics {name}`warm` with the diagnostics {name}`cold` of a
cold elaboration. A diagnostic that occurs more often on one side than on the other is listed once
for each extra occurrence.
-/
public def ColdComparison.of (warm cold : Array TextDiagnostic) : ColdComparison where
  onlyWarm := cold.foldl Array.erase warm |>.map (·.describe)
  onlyCold := warm.foldl Array.erase cold |>.map (·.describe)

/-- The reuse in a language server session that replays edit sequences. -/
public structure ReuseReport where
  /-- The total block size of the base document. -/
  baseTotal : Nat
  /-- The number of errors in the base document. -/
  baseErrors : Nat
  sequences : Array SequenceReuse
  /-- The cold comparison, which is made only with {name}`ReuseOptions.cold`. -/
  cold? : Option ColdComparison := none
deriving BEq, Repr, Inhabited

/-- Describes the reuse after an edit on one line. -/
def EditReuse.describe (r : EditReuse) : String := s!"{r.result.describe} errors {r.errors}"

/--
The text of a reuse report. It starts with the total block size and the number of errors of the base
document. For each edit sequence, a line with the sequence's label is followed by a line with the
reused size, the reusable size, the total, the source of the reuse boundary and the number of
errors. With {name}`ReuseOptions.each`, a line for each LSP edit comes between the two. With
{name}`ReuseOptions.cold`, the report ends with whether the session's diagnostics match those of a
cold elaboration. The diagnostics that differ follow, with the later lines of each one indented by
four spaces.
-/
public def ReuseReport.render (r : ReuseReport) : String := Id.run do
  let mut out := s!"base: total {r.baseTotal} errors {r.baseErrors}\n"
  for s in r.sequences, i in [1:r.sequences.size + 1] do
    out := out ++ s!"edit {i} {s.label}\n"
    for state in s.states, j in [1:s.states.size + 1] do
      out := out ++ s!"  state {j}: {state.describe}\n"
    out := out ++ s!"  {s.final.describe}\n"
  if let some c := r.cold? then
    if c.onlyWarm.isEmpty && c.onlyCold.isEmpty then out := out ++ "cold: diagnostics match\n"
    else
      out := out ++ "cold: diagnostics differ\n"
      -- The later lines of a diagnostic are indented further than the first.
      let indented (d : String) := d.replace "\n" "\n    "
      for d in c.onlyWarm do out := out ++ s!"  - {indented d}\n"
      for d in c.onlyCold do out := out ++ s!"  + {indented d}\n"
  return out

/-- Reads the reuse after an edit from its line of a reuse report. -/
def EditReuse.parse (line : String.Slice) : Except String EditReuse := do
  let nat (w : String.Slice) : Except String Nat :=
    match w.toNat? with
    | some n => pure n
    | none => throw s!"expected a number, found '{w.copy}' in '{line.copy}'"
  match (line.trimAscii.split ' ').toArray with
  | #[r, reused, _, ru, reusable, _, t, total, b, source, source', e, errors] =>
    unless r == "reused".toSlice && ru == "reusable".toSlice && t == "total".toSlice &&
        b == "boundary".toSlice && e == "errors".toSlice do
      throw s!"not a line of reuse: '{line.copy}'"
    let words := s!"{source} {source'}"
    let some boundarySource :=
        [BoundarySource.reuseStopped, .enclosingBlock].find? (·.describe == words)
      | throw s!"unknown boundary source in '{line.copy}'"
    let result : ReuseResult :=
      { reused := ← nat reused, reusable := ← nat reusable, total := ← nat total, boundarySource }
    return { result, errors := ← nat errors }
  | _ => throw s!"not a line of reuse: '{line.copy}'"

/--
Reads a reuse report from its text, as {name}`ReuseReport.render` gives it. The percentages are
ignored, since they follow from the sizes.
-/
public def ReuseReport.parse (text : String) : Except String ReuseReport := do
  let mut base? : Option (Nat × Nat) := none
  let mut sequences : Array SequenceReuse := #[]
  -- The label and the states of the edit sequence whose final line is still to come
  let mut pending : Option (String × Array EditReuse) := none
  let mut cold? : Option ColdComparison := none
  for line in text.lines do
    if let some c := cold? then
      -- A line of a cold comparison is a new diagnostic or, indented by four spaces, the next
      -- line of the previous one.
      if let some next := line.dropPrefix? "    " then
        let continued (ds : Array String) := ds.modify (ds.size - 1) (· ++ "\n" ++ next.copy)
        if !c.onlyCold.isEmpty then cold? := some { c with onlyCold := continued c.onlyCold }
        else if !c.onlyWarm.isEmpty then cold? := some { c with onlyWarm := continued c.onlyWarm }
        else throw s!"a continuation line without a diagnostic: '{line.copy}'"
      else if let some d := line.dropPrefix? "  - " then
        cold? := some { c with onlyWarm := c.onlyWarm.push d.copy }
      else if let some d := line.dropPrefix? "  + " then
        cold? := some { c with onlyCold := c.onlyCold.push d.copy }
      else throw s!"unexpected line in the cold comparison: '{line.copy}'"
    else if let some rest := line.dropPrefix? "base: " then
      match (rest.split ' ').toArray with
      | #[t, total, e, errors] =>
        match t == "total".toSlice && e == "errors".toSlice, total.toNat?, errors.toNat? with
        | true, some total, some errors => base? := some (total, errors)
        | _, _, _ => throw s!"not a line of the base document: '{line.copy}'"
      | _ => throw s!"not a line of the base document: '{line.copy}'"
    else if let some rest := line.dropPrefix? "edit " then
      if pending.isSome then throw s!"an edit sequence without its result before '{line.copy}'"
      pending := some ((rest.dropWhile (· != ' ')).drop 1 |>.copy, #[])
    else if let some rest := line.dropPrefix? "  state " then
      let some (label, states) := pending
        | throw s!"a state outside an edit sequence: '{line.copy}'"
      let state ← EditReuse.parse (rest.dropWhile (· != ' '))
      pending := some (label, states.push state)
    else if line.startsWith "  " then
      let some (label, states) := pending
        | throw s!"a result outside an edit sequence: '{line.copy}'"
      sequences := sequences.push { label, states, final := ← EditReuse.parse line }
      pending := none
    else if line == "cold: diagnostics match".toSlice ||
        line == "cold: diagnostics differ".toSlice then
      cold? := some {}
    else throw s!"unexpected line in a reuse report: '{line.copy}'"
  if pending.isSome then throw "the last edit sequence has no result"
  let some (baseTotal, baseErrors) := base? | throw "the reuse report has no base document"
  return { baseTotal, baseErrors, sequences, cold? }

/--
Measures reuse after an edit whose first changed character is at {name}`editPos`. {name}`before` are
the block outlines before the edit, {name}`prev` the diagnostics before the edit, and {name}`text`
and {name}`diags` the text and the diagnostics after it.
-/
def measureEdit (before : Array BlockOutline) (prev : Array TextDiagnostic) (text : String)
    (diags : Array TextDiagnostic) (editPos : String.Pos.Raw) : EditReuse :=
  let fileMap := FileMap.ofString text
  let stops := diags.filter isReuseStopped |>.map fun d => (d, fileMap.lspPosToUtf8Pos d.pos)
  let newStops := stops.filter fun (d, pos) => isNew prev diags d pos
  let errors := diags.filter (·.severity == "error") |>.size
  let result :=
    measure before editPos (stops.map (·.2)) (blockOutlines diags) (newStops.map (·.2))
  { result, errors }

/--
Replays edit sequences in a session of the language server in the Lake workspace at {name}`root` and
reports the reuse after each one. The document is written to {name}`path`.

The edit position of a sequence is the first character that the sequence changed, and the block
outline before the edit is the one after the previous sequence. With {name}`ReuseOptions.cold`, the
server then opens the final text again for a cold elaboration, and the cold comparison leaves out
{lit}`reuse stopped` messages and the times of `Elab.Verso.blocks` messages. Edit sequences whose
number differs from the number of their labels are an error, which names {name}`path`.
-/
public def reuseReport (root path : System.FilePath) (seqs : EditSequences)
    (opts : ReuseOptions := {}) : IO ReuseReport := do
  IO.ofExcept <| seqs.checkLabels path
  withServer root #["-Dtrace.Elab.reuse=true", "-Dtrace.Elab.Verso.blocks=true"] fun server => do
    let doc ← server.openDoc path seqs.base
    let mut diags ← doc.diagnostics
    let mut blocks := blockOutlines diags
    let baseTotal := totalSize blocks
    let baseErrors := diags.filter (·.severity == "error") |>.size
    let mut sequences := #[]
    let mut text := seqs.base
    for (seq, label) in seqs.sequences.zip seqs.labels do
      let before := blocks
      let prev := diags
      let initial := text
      let mut states := #[]
      for e in seq do
        let old := text
        text := applyTextEdit text e
        doc.change e
        if opts.each then
          let diags' ← doc.diagnostics
          states := states.push (measureEdit blocks diags text diags' (old.firstDiffPos text))
          blocks := blockOutlines diags'
          diags := diags'
      let diags' ← doc.diagnostics
      let final := measureEdit before prev text diags' (initial.firstDiffPos text)
      sequences := sequences.push { label, states, final }
      blocks := blockOutlines diags'
      diags := diags'
    let mut cold? := none
    if opts.cold then
      -- The times at which blocks were elaborated differ between the two elaborations.
      let untimed (d : TextDiagnostic) := { d with text := stripElaborationTime d.text }
      let warm := (← doc.diagnostics).filter (!isReuseStopped ·) |>.map untimed
      doc.close
      doc.reopen text
      let cold := (← doc.diagnostics).filter (!isReuseStopped ·) |>.map untimed
      cold? := some (ColdComparison.of warm cold)
    return { baseTotal, baseErrors, sequences, cold? }

/--
The ranges of the command snapshots of the first elaboration of {name}`text`, one line each, from
the messages of {option}`trace.Elab.snapshotTree`. Each range is the first one in the command's
snapshot tree, as Lean renders it. The server runs in the Lake workspace at {name}`root`, and the
document is written to {name}`path`.
-/
public def snapshotTree (root path : System.FilePath) (text : String) : IO String :=
  withServer root #["-Dtrace.Elab.snapshotTree=true"] fun server => do
    let doc ← server.openDoc path text
    let mut out := ""
    for d in ← doc.diagnostics do
      if d.text.startsWith "[Elab.snapshotTree]" then
        for line in d.text.split '\n' do
          if line.contains "⟩-⟨" then
            out := out ++ (line.dropWhile (· != '⟨')).trimAsciiEnd.copy ++ "\n"
            break
    return out
