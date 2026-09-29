/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

import Cli
import VersoGen.Server

set_option doc.verso true

open Cli VersoGen.Edit VersoGen.Server

/--
The root of the repository that contains the benchmark. The benchmark's commands run from it, so it
is the current directory. The language server runs in the repository's Lake workspace.
-/
def repositoryRoot : System.FilePath := "."

/--
The directory of the benchmark's corpus and recorded results, relative to {name}`repositoryRoot`.
-/
def benchDir : System.FilePath := "bench" / "reuse"

/-- The file that a document of the benchmark is written to before the language server opens it. -/
def docPath (input : System.FilePath) : System.FilePath :=
  scratchDir repositoryRoot "reuse-bench" / s!"{input.fileStem.getD "doc"}.lean"

def runReuse (p : Parsed) : IO UInt32 := do
  let input : System.FilePath := p.positionalArg! "edits" |>.as! String
  let opts : ReuseOptions := { each := p.hasFlag "each", cold := p.hasFlag "cold" }
  let report ← reuseReport repositoryRoot (docPath input) (← EditSequences.load input) opts
  IO.print report.render
  return 0

def runRecord (_ : Parsed) : IO UInt32 := do
  for input in ← corpusScripts (benchDir / "corpus") do
    let report ← reuseReport repositoryRoot (docPath input) (← EditSequences.load input)
    let out := benchDir / "expected" / s!"{input.fileStem.getD "doc"}.txt"
    IO.FS.writeFile out report.render
    IO.println s!"{out}"
  return 0

def runSnapshotTree (p : Parsed) : IO UInt32 := do
  let input : System.FilePath := p.positionalArg! "edits" |>.as! String
  IO.print (← snapshotTree repositoryRoot (docPath input) (← EditSequences.load input).base)
  return 0

def runLspCheck (p : Parsed) : IO UInt32 := do
  let mut ok := true
  for input in p.variableArgsAs! String do
    let script ← EditScript.load input
    let some genre := profile? script.profile
      | IO.eprintln s!"{input}: unknown genre profile {script.profile}"; return 1
    let name := (input : System.FilePath).fileStem.getD "doc"
    let (report, passed) ← checkAnswers repositoryRoot (docPath input) genre script.base name
    IO.print report
    ok := ok && passed
  return if ok then 0 else 1

def runTime (p : Parsed) : IO UInt32 := do
  let time ← reElabTime repositoryRoot (p.positionalArg! "file" |>.as! String)
    (p.positionalArg! "new-text" |>.as! String) (p.positionalArg! "line" |>.as! Nat)
    (p.positionalArg! "character" |>.as! Nat)
  IO.println s!"re-elab time={time}"
  return 0

def reuseCmd : Cmd := `[Cli|
  reuse VIA runReuse;
  "Replays an edit script, or edit sequences, from <edits>. For each edit sequence, it prints the \
    reused size and the reusable size, each with its percentage of the total size of the \
    document's top-level blocks, and then that total size. Each size is a number of blocks, \
    counted as bench/reuse/README.md describes. It also tells whether the reuse boundary, the position up \
    to which blocks count as reused (bench/reuse/README.md defines it), came from `trace.Elab.reuse` or is the start of the edited top-level block."

  FLAGS:
    each;                  "Also report after each LSP edit."
    cold;                  "Compare the session's diagnostics at the end with those of a cold \
                             elaboration."

  ARGS:
    edits : String;        "The file with the edit script or edit sequences."
]

def recordCmd : Cmd := `[Cli|
  record VIA runRecord;
  "Replays each edit script in `bench/reuse/corpus` and writes its reuse report to \
    `bench/reuse/expected`, in the file with the script's name and the extension `.txt`."
]

def snapshotTreeCmd : Cmd := `[Cli|
  "snapshot-tree" VIA runSnapshotTree;
  "Prints the snapshot tree of the base document's first elaboration."

  ARGS:
    edits : String;        "The file with the edit script or edit sequences."
]

def lspCheckCmd : Cmd := `[Cli|
  "lsp-check" VIA runLspCheck;
  "Checks the language server's answers for the base document of each edit script against the \
    surface document that it was concretized from, prints a report and exits with status 1 if a \
    check fails."

  ARGS:
    ...edits : String;     "The files with the edit scripts."
]

def timeCmd : Cmd := `[Cli|
  time VIA runTime;
  "Opens <file>, inserts <new-text> at <line> and <character>, and prints the time in milliseconds \
    until the server has processed the file again. For a <new-text> that starts with a dash, write \
    `time -- <file> <new-text> <line> <character>`."

  ARGS:
    file : String;         "The Lean file to open."
    "new-text" : String;   "The text to insert."
    line : Nat;            "The line of the insertion, counted from 0."
    character : Nat;       "The character of the insertion in its line, counted from 0."
]

/-- Prints the command's help and returns 1, for a command line without a subcommand. -/
def printHelp (p : Parsed) : IO UInt32 := do
  p.printHelp
  return 1

def reuseBenchCmd : Cmd := `[Cli|
  "verso-internal-reuse-bench" VIA printHelp;
  "The reuse benchmark, which replays edit scripts in the language server and reports the server's \
    reuse. It runs from the repository root."

  SUBCOMMANDS:
    reuseCmd;
    recordCmd;
    snapshotTreeCmd;
    lspCheckCmd;
    timeCmd
]

public def main (args : List String) : IO UInt32 :=
  reuseBenchCmd.validate args
