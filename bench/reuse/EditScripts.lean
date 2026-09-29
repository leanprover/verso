/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoGen.Edit.Script

set_option doc.verso true

open VersoGen.Edit VersoGen.Genre VersoGen.TextEdit

def usage : String :=
  "usage:
  verso-internal-edit-scripts generate <profile> <seed> <edit-chance> <out.json>
    [--blocks <n>] [--parts <n>] [--proof-weight <ms>]
  verso-internal-edit-scripts write <edits.json> <dir>

`generate` generates a document from a genre profile (minimal or manual) and a seed and then edits
it. <edit-chance> is the chance, in percent, that the generator edits each node. `write` reads an
edit script or edit sequences. It writes the base document and the document after each edit
sequence as Lean files in <dir>."

def parseParams (params : Params) : List String → Except String Params
  | [] => pure params
  | "--blocks" :: n :: rest => do parseParams { params with topLevelBlocks := ← nat n } rest
  | "--parts" :: n :: rest => do parseParams { params with parts := ← nat n } rest
  | "--proof-weight" :: n :: rest => do parseParams { params with proofWeight := ← nat n } rest
  | arg :: _ => throw s!"unknown option {arg}"
where
  nat (s : String) : Except String Nat := s.toNat?.elim (throw s!"not a number: {s}") pure

def main (args : List String) : IO UInt32 := do
  match args with
  | "generate" :: profile :: seed :: editChance :: out :: rest =>
    let some p := profile? profile
      | IO.eprintln s!"unknown genre profile {profile}"; return 1
    let (some seed, some editChance) := (seed.toNat?, editChance.toNat?)
      | IO.eprintln usage; return 1
    match parseParams {} rest with
    | .error e => IO.eprintln s!"{e}\n{usage}"; return 1
    | .ok params =>
      let script := generateScript p params seed editChance
      script.save out
      IO.println s!"{out}: {script.edits.size} edits"
      return 0
  | ["write", input, dir] =>
    let seqs ← EditSequences.load input
    let stem := (input : System.FilePath).fileStem.getD "doc"
    let mut text := seqs.base
    IO.FS.createDirAll dir
    IO.FS.writeFile ((dir : System.FilePath) / s!"{stem}_0.lean") text
    for seq in seqs.sequences, i in [1:seqs.sequences.size + 1] do
      text := seq.foldl applyTextEdit text
      IO.FS.writeFile ((dir : System.FilePath) / s!"{stem}_{i}.lean") text
    return 0
  | _ => IO.eprintln usage; return 1
