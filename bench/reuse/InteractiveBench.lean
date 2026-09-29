/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoGen.Server

set_option doc.verso true

open VersoGen.Edit VersoGen.Server

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

def usage : String :=
  "usage:
  verso-internal-reuse-bench reuse <edits.json> [--each] [--cold]
  verso-internal-reuse-bench record
  verso-internal-reuse-bench snapshot-tree <edits.json>
  verso-internal-reuse-bench lsp-check <edits.json>...
  verso-internal-reuse-bench time <file> <new-text> <line> <character>

`reuse` replays an edit script, or edit sequences, from <edits.json>. For each edit sequence, it
prints the reused size and the reusable size, each with its percentage of the total, and then the
total. It also tells whether the reuse boundary came from `trace.Elab.reuse` or is the start of the
edited top-level block. With --each it also reports after each LSP edit, and with --cold it compares
the session's diagnostics at the end with those of a cold elaboration.

`record` replays each edit script in `bench/reuse/corpus` and writes its reuse to
`bench/reuse/expected`.

`snapshot-tree` prints the snapshot tree of the base document's first elaboration.

`lsp-check` checks the language server's answers for the base document of each edit script against
the surface document that it was concretized from, prints a report and exits with status 1 if a
check fails.

`time` opens <file>, inserts <new-text> at <line> and <character>, both counted from 0, and prints
the time in milliseconds until the server has processed the file again."

def parseReuseOptions : List String → Except String ReuseOptions
  | [] => pure {}
  | "--each" :: rest => return { ← parseReuseOptions rest with each := true }
  | "--cold" :: rest => return { ← parseReuseOptions rest with cold := true }
  | arg :: _ => throw s!"unknown option {arg}"

def main (args : List String) : IO UInt32 := do
  match args with
  | "reuse" :: input :: rest =>
    match parseReuseOptions rest with
    | .ok opts =>
      let report ← reuseReport repositoryRoot (docPath input) (← EditSequences.load input) opts
      IO.print report.render
      return 0
    | .error e => IO.eprintln s!"{e}\n{usage}"; return 1
  | ["record"] =>
    for input in ← corpusScripts (benchDir / "corpus") do
      let report ← reuseReport repositoryRoot (docPath input) (← EditSequences.load input)
      let out := benchDir / "expected" / s!"{input.fileStem.getD "doc"}.txt"
      IO.FS.writeFile out report.render
      IO.println s!"{out}"
    return 0
  | ["snapshot-tree", input] =>
    IO.print (← snapshotTree repositoryRoot (docPath input) (← EditSequences.load input).base)
    return 0
  | "lsp-check" :: inputs =>
    let mut ok := true
    for input in inputs do
      let script ← EditScript.load input
      let some p := profile? script.profile
        | IO.eprintln s!"{input}: unknown genre profile {script.profile}"; return 1
      let name := (input : System.FilePath).fileStem.getD "doc"
      let (report, passed) ← checkAnswers repositoryRoot (docPath input) p script.base name
      IO.print report
      ok := ok && passed
    return if ok then 0 else 1
  | ["time", path, newText, line, character] =>
    let (some line, some character) := (line.toNat?, character.toNat?)
      | IO.eprintln usage; return 1
    IO.println s!"re-elab time={← reElabTime repositoryRoot path newText line character}"
    return 0
  | _ => IO.eprintln usage; return 1
