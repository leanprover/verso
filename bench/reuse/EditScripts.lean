/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

import Cli
import VersoGen.Edit.Script

set_option doc.verso true

open Cli VersoGen.Edit VersoGen.Genre VersoGen.TextEdit

def runGenerate (p : Parsed) : IO UInt32 := do
  let profile := p.positionalArg! "profile" |>.as! String
  let some genre := profile? profile
    | p.printError s!"unknown genre profile {profile}"; return 1
  let out := p.positionalArg! "out" |>.as! String
  let params : Params := {
    topLevelBlocks := p.flag! "blocks" |>.as! Nat
    parts := p.flag! "parts" |>.as! Nat
    proofWeight := p.flag! "proof-weight" |>.as! Nat
  }
  let script := generateScript genre params (p.positionalArg! "seed" |>.as! Nat)
    (p.positionalArg! "edit-chance" |>.as! Nat)
  script.save out
  IO.println s!"{out}: {script.edits.size} edits"
  return 0

def runWrite (p : Parsed) : IO UInt32 := do
  let input : System.FilePath := p.positionalArg! "edits" |>.as! String
  let dir : System.FilePath := p.positionalArg! "dir" |>.as! String
  let seqs ← EditSequences.load input
  let stem := input.fileStem.getD "doc"
  let mut text := seqs.base
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / s!"{stem}_0.lean") text
  for seq in seqs.sequences, i in [1:seqs.sequences.size + 1] do
    text := seq.foldl applyTextEdit text
    IO.FS.writeFile (dir / s!"{stem}_{i}.lean") text
  return 0

def generateCmd : Cmd := `[Cli|
  generate VIA runGenerate;
  "Generates a document from a genre profile and a seed, then edits it, and writes the edit script \
    to <out>."

  FLAGS:
    blocks : Nat;          "The number of top-level blocks."
    parts : Nat;           "The number of parts below the document."
    "proof-weight" : Nat;  "How long each proof in generated Lean code sleeps, in milliseconds."

  ARGS:
    profile : String;      "The genre profile: minimal or manual."
    seed : Nat;            "The seed of the document and its edits."
    "edit-chance" : Nat;   "The chance, in percent, that the generator edits each node."
    out : String;          "The file that the edit script is written to."

  EXTENSIONS:
    defaultValues! #[("blocks", toString ({} : Params).topLevelBlocks),
      ("parts", toString ({} : Params).parts),
      ("proof-weight", toString ({} : Params).proofWeight)]
]

def writeCmd : Cmd := `[Cli|
  write VIA runWrite;
  "Reads an edit script or edit sequences, and writes the base document and the document after \
    each edit sequence as Lean files in <dir>."

  ARGS:
    edits : String;        "The file with the edit script or edit sequences."
    dir : String;          "The directory that the Lean files are written to."
]

/-- Prints the command's help and returns 1, for a command line without a subcommand. -/
def printHelp (p : Parsed) : IO UInt32 := do
  p.printHelp
  return 1

def editScriptsCmd : Cmd := `[Cli|
  "verso-internal-edit-scripts" VIA printHelp;
  "Generates the reuse benchmark's edit scripts and writes their documents as Lean files."

  SUBCOMMANDS:
    generateCmd;
    writeCmd
]

public def main (args : List String) : IO UInt32 :=
  editScriptsCmd.validate args
