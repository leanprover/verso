/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.Edit.Construct
public import VersoGen.TextEdit.Split
public import VersoGen.TextEdit.Permute
public import VersoGen.Doc.Concretize
public import VersoGen.Genre.Minimal
public import VersoGen.Genre.Manual

set_option doc.verso true

/-!
Edit scripts, which record surface document edits as JSON for the tests and benchmarks. Replaying
an edit script concretizes the surface document before and after each edit and computes the
textual difference. The edit's splitting strategy splits the difference into replacements, which
are reordered if the edit has a reordering seed and then become LSP edits.
-/

namespace VersoGen.Edit

open VersoGen.Doc VersoGen.Doc.SurfaceDoc VersoGen.Genre VersoGen.Random VersoGen.TextEdit

open Lean

/-- The genre profiles that edit scripts may refer to. -/
public def profiles : List GenreProfile := [minimalProfile, manualProfile]

/-- The genre profile with the given name, if there is one. -/
public def profile? (name : String) : Option GenreProfile := profiles.find? (·.name == name)

/--
A surface document edit in an edit script, with how its textual difference becomes LSP edits.
-/
public structure ScriptEdit where
  /--
  The number of nodes that the traversal moves forward in document order, one
  {name}`Zipper.next?` at a time, to reach the node where the edit is made. The traversal starts at
  the node where the previous edit left the zipper, or at the root part for the first edit. Replay
  moves that many nodes forward and then makes the edit.
  -/
  steps : Nat
  edit : Edit
  split : SplitStrategy
  /-- The seed of the splitting strategy's random choices. -/
  splitSeed : Nat
  /--
  The seed of a reordering of the split replacements before they become LSP edits, or
  {name}`none` to keep the order of the splitting strategy. From the seed,
  {name}`swapsToRandomOrder` draws the exchanges of consecutive replacements that bubble passes
  toward a random order would make. {name}`permute` applies them in order, whether or not an
  earlier exchange was refused.
  -/
  permuteSeed? : Option Nat := none
deriving ToJson, FromJson, BEq, Repr, Inhabited

/-- Where an edit script came from. -/
public inductive Provenance where
  /--
  Generated from parameters and a seed. {name}`editChance` is the chance, in percent, that the
  generator edits each node that it visits.
  -/
  | generated (params : Params) (seed editChance : Nat)
  /-- Written as edits at paths. -/
  | byPath
deriving ToJson, FromJson, Repr, Inhabited

/-- A base surface document with edits to replay on it. -/
public structure EditScript where
  /-- The name of the genre profile. -/
  profile : String
  provenance : Provenance
  base : Part
  edits : Array ScriptEdit
deriving ToJson, FromJson, Repr, Inhabited

public def EditScript.recorded (s : EditScript) : List RecordedEdit :=
  s.edits.toList.map fun e => ⟨e.steps, e.edit⟩

/--
The concretized texts of an edit script's surface documents and the LSP edit sequences between
them.
-/
public structure Replayed where
  /-- The text of the base surface document, then the text after each surface document edit. -/
  texts : Array String
  /-- The LSP edit sequence of each surface document edit. -/
  sequences : Array (Array Lsp.TextEdit)
deriving Inhabited

/--
The surface documents of an edit script: the base surface document, then the surface document after
each edit. The surface document after {lit}`k` edits is {name}`replayDoc` of the first {lit}`k`
recorded edits.
-/
def EditScript.surfaceDocs (s : EditScript) : Except String (Array Part) := do
  let mut z : Zipper := .start s.base
  let mut out := #[z.root]
  for e in s.edits, k in [0:s.edits.size] do
    let some z' := z.nextN e.steps >>= e.edit.apply
      | throw s!"edit {k} doesn't apply: {repr (some e.edit)}"
    z := z'
    out := out.push z.root
  return out

/-- Replays an edit script, giving its concretized texts and its LSP edit sequences. -/
public def EditScript.replay (s : EditScript) : Except String Replayed := do
  let some p := profile? s.profile
    | throw s!"unknown genre profile '{s.profile}'"
  let texts := (← s.surfaceDocs).map (concretizeDocument p)
  let sequences := s.edits.zipIdx.map fun (e, i) =>
    let diff := textDiff texts[i]! texts[i + 1]!
    let reps := runWithSeed (splitReplacements e.split diff) e.splitSeed
    let reps := match e.permuteSeed? with
      | some seed => permute (runWithSeed (swapsToRandomOrder reps.size) seed) reps
      | none => reps
    toLspEdits texts[i]! reps
  return { texts, sequences }

/--
Generates an edit script: a document of the genre profile and edits of it, each with a random
splitting strategy.
-/
public def generateScript (p : GenreProfile) (params : Params) (seed editChance : Nat)
    (strategies : List SplitStrategy := [.wholeHunks, .typing, .garbage]) : EditScript :=
  LoremGen.runWithSeed (seed := seed) do
    let base ← genDocument p params
    let (_, recorded) ← generateEdits p params editChance base
    let mut edits := #[]
    for r in recorded do
      edits := edits.push {
        steps := r.steps, edit := r.edit,
        split := ← Plausible.Gen.oneOfWithDefault (pure .wholeHunks) (strategies.map pure),
        splitSeed := (← Plausible.Gen.choose Nat 0 (2 ^ 30) (Nat.zero_le _)).val
      }
    return { profile := p.name, provenance := .generated params seed editChance, base, edits }

/-- Makes an edit script from edits at paths, each with a splitting strategy. -/
public def pathScript (p : GenreProfile) (base : Part) (edits : List (PathEdit × SplitStrategy)) :
    Except String EditScript := do
  let recorded ← recordAtPath p base (edits.map (·.1))
  let edits := (recorded.zip edits).toArray.zipIdx.map fun ((r, (_, split)), i) =>
    { steps := r.steps, edit := r.edit, split, splitSeed := i }
  return { profile := p.name, provenance := .byPath, base, edits }

/--
A base text with LSP edit sequences to apply to it in order. Replaying an edit script gives one, and
tests can write one directly for edits that surface documents don't describe.
-/
public structure EditSequences where
  base : String
  sequences : Array (Array Lsp.TextEdit)
  /-- What each sequence does, for people reading results. -/
  labels : Array String
deriving ToJson, FromJson, Inhabited

/-- The name of an edit's kind. -/
def Edit.kindName : Edit → String
  | .part e => constructorName (toJson e)
  | .inlines e => constructorName (toJson e)
  | .directive _ => "changeDirective"
  | .command _ => "changeCommandArgs"
  | .code _ => "changeLines"
  | .linkDef _ => "changeLinkDef"
  | .footnoteDef _ => "changeFootnoteDef"
  | .reference _ => "reference"
  | .contents _ => "insertContents"
  | .sibling e =>
    match e with
    | .insert .. => "insertSibling"
    | .delete .. => "deleteSibling"
    | .wrap .. => "wrap"
    | .deparent .. => "deparent"
    | .reparent .. => "reparent"
where
  /-- The name of the constructor in the JSON encoding of a value of an inductive type. -/
  constructorName : Json → String
    | .obj kvs => kvs.toArray[0]?.map (·.1) |>.getD "edit"
    | .str s => s
    | _ => "edit"

/-- The edit sequences of an edit script, labeled with each edit's kind and splitting strategy. -/
public def EditScript.sequences (s : EditScript) : Except String EditSequences := do
  let r ← s.replay
  let labels := s.edits.map fun e =>
    let split := match toJson e.split with
      | .str x => x
      | j => j.compress
    s!"{e.edit.kindName} {split}"
  return { base := r.texts[0]!, sequences := r.sequences, labels }

/--
Checks that each edit sequence has exactly one label. The error names {name}`file`, the file that
the sequences belong to.
-/
public def EditSequences.checkLabels (seqs : EditSequences) (file : System.FilePath) :
    Except String Unit := do
  unless seqs.sequences.size == seqs.labels.size do
    throw s!"{file}: the numbers of edit sequences ({seqs.sequences.size}) and labels \
      ({seqs.labels.size}) differ"

/--
Reads edit sequences from a JSON file that contains either an edit script or edit sequences. Edit
sequences whose number differs from the number of their labels are an error.
-/
public def EditSequences.load (file : System.FilePath) : IO EditSequences := do
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile file)
  if (json.getObjVal? "profile").isOk then
    let script : EditScript ← IO.ofExcept <| fromJson? json
    IO.ofExcept script.sequences
  else
    let seqs : EditSequences ← IO.ofExcept <| fromJson? json
    IO.ofExcept <| seqs.checkLabels file
    return seqs

/-- Writes a value to a JSON file, creating its directory. -/
public def saveJson [ToJson α] (x : α) (file : System.FilePath) : IO Unit := do
  if let some dir := file.parent then IO.FS.createDirAll dir
  IO.FS.writeFile file ((toJson x).pretty ++ "\n")

public def EditScript.load (file : System.FilePath) : IO EditScript := do
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile file)
  IO.ofExcept <| fromJson? json

public def EditScript.save (s : EditScript) (file : System.FilePath) : IO Unit := saveJson s file

/-- The JSON files of a corpus directory, in the order of their names. -/
public def corpusScripts (dir : System.FilePath) : IO (Array System.FilePath) := do
  let files ← dir.readDir
  return (files.map (·.path) |>.filter (·.extension == some "json")).qsort (·.toString < ·.toString)
