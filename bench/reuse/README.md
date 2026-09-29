# Reuse Benchmark

This benchmark measures how much of a Verso document the Lean language
server reuses after an edit. It replays a fixed corpus of recorded
edits in the language server and records, for each edit, how much the
server reused and how much it could have theoretically reused. The
recorded results are the baseline that work on Verso's incremental
elaboration is measured against. Deviations from the baseline are test
failures, so they don't go unnoticed. Improvements should be
committed, and regressions carefully thought about.

## Reused and Reusable Sizes

Reuse after an edit is measured in blocks. The block size of a block
is the number of blocks in its syntax, including the block itself,
with list items and description list items counted as blocks. For
example, paragraphs have size 1, and directives that contain two
paragraphs have size 3. The total size is the sum of the sizes of the
document's top-level blocks. After each edit, the benchmark reports
two sizes, each with its percentage of the total:

- The _reused size_ is the total size of the blocks that the server in
  fact reused. With the trace class `Elab.Verso.blocks` enabled, Verso
  reports each top-level block that it elaborates, with the range and
  size of every block in it. With `trace.Elab.reuse` enabled, Lean
  reports where reuse stopped, the _reuse boundary_. The blocks that
  end at or before the reuse boundary count as reused.
- The _reusable size_ is the total size of the blocks that the edit
  left unchanged and which the server could have reused. Blocks are
  considered unchanged if they end before the first character was
  edited. Blocks that end at that character are unchanged only if the
  text after the edit has a block with the same source range (measured
  in byte offsets), size and digest of its text, because text typed at
  the end of a block usually extends it.

When a block counts as reused or unchanged, so do all of its
sub-blocks. Otherwise, the sub-blocks are counted individually. When
the reused size is below the reusable size, the difference is reuse
that the server misses. Better incremental elaboration reduces the
amount of missed reuse.

## Edit Scripts

Testing incrementality in practice relies on being able to simulate
user behavior. Real documents are typically not instantly replaced
with new ones; inestead, they start off in a well-formed state, then
pass through a sequence of states that contain syntactic or
elaboration errors, eventually arriving in a new well-formed state to
be compared. This process is simulated using generated edit scripts.

The documents and edits come from the `VersoGen` library in
`src/verso-gen/`, which generates random Verso documents and edits for
tests and benchmarks. It represents documents as _surface documents_:
trees with the structure of Verso's concrete syntax. Surface documents
are _concretized_ into the text of Lean files. The generator follows a
_genre profile_, which gives, for the documents of one genre, their
imports and the directives, code blocks, block commands, roles and
metadata that they may use. The profile `minimal` is for a small test
genre. The profile `manual` is for Verso's `Manual` genre. Manual
documents contain Lean code blocks with definitions and theorems.

An _edit script_ is a structural edit script over surface documents.
It consists of a base surface document and a sequence of structural
edits to it, such as inserting a paragraph, removing a block, wrapping
blocks in a directive or changing the text of an inline. Replaying an
edit script gives the surface document after each edit.

The language server receives text edits, so each structural edit is
turned into an _edit sequence_, the sequence of LSP text edits that
the benchmark sends to the server. Edit sequences are derived from
structural edits in five steps:

1. The surface documents before and after the edit are concretized
   into text.
2. The difference between the two texts is computed as replacements of
   ranges of the text.
3. The replacements are split into changes that an editor might send
   over LSP: whole replacements, like a paste; the new text typed a
   few characters at a time; or a short piece of nonsense inserted
   first and removed after the replacement, which leaves the document
   with syntax errors in between.
4. Based on a permutation seed, the order of the split replacements is
   shuffled.
5. The replacements become LSP text edits.

These text edits are then applied over an LSP connection to the Lean
language server to simulate a user.

## Saved Scripts

In this code, "edit script" always refers to structural scripts, and
"edit sequence" to the LSP text edits derived from an edit script's
step. Edit scripts are stored as JSON. The format is defined by the
`ToJson` and `FromJson` instances of `EditScript`, `ScriptEdit` and
`Provenance` in `src/verso-gen/VersoGen/Edit/Script.lean`, and the
structural edits are the constructors of `Edit` in
`src/verso-gen/VersoGen/Edit/Basic.lean`. Scripts have this shape:

```json
{"profile": "minimal",
 "provenance": {"generated": {"seed": 1, "params": {…}, "editChance": 10}},
 "base": {…},
 "edits": [{"steps": 24, "edit": {…}, "split": "garbage", "splitSeed": 340555834}, …]}
```

The field `provenance` records how the script was made. The `steps`
field records the position of an edit; it corresponds to traversing
through N nodes of the document before arriving at the edit location.
The first `steps` field counts from the document root, while
subsequent fields count from the location of the prior edit.

## The Corpus

The corpus in `corpus/` consists of edit scripts that were made with
`verso-internal-edit-scripts generate`. Each script's `profile` field
records its genre profile, and its `provenance` field records the
generator's parameters, the seed and the edit chance. The edit chance
is the chance, in percent, that the generator edits each node that it
visits.

| Script                      | Genre profile | Seed | Edit chance | Top-level blocks | Parts | Proof weight |
| --------------------------- | ------------- | ---- | ----------- | ---------------- | ----- | ------------ |
| `minimal-1.json`            | minimal       | 1    | 10          | 12               | 3     | 0            |
| `minimal-large-2.json`      | minimal       | 2    | 8           | 60               | 8     | 0            |
| `manual-1.json`             | manual        | 1    | 10          | 12               | 3     | 0            |
| `manual-slow-proofs-3.json` | manual        | 3    | 10          | 12               | 3     | 50           |

The proof weight is the time in milliseconds that each proof in a
generated Lean code block sleeps. In `manual-slow-proofs-3.json`, it
makes elaborating a code block again cost measurable time. One edit of
`minimal-large-2.json` has a `permuteSeed`, which
`verso-internal-edit-scripts generate` doesn't write, so the field is
added by hand when that script is generated again.

## What the Benchmark Records

The directory `expected/` contains the benchmark's results:

- For each script in the corpus, a file with the same name and the
  extension `.txt` records the reuse after each of the script's edits.
  It starts with the total size and the number of errors of the base
  document. For each edit, it gives the edit's kind and splitting
  strategy, the reused and reusable sizes with their percentages, the
  total size, whether the reuse boundary came from a
  `trace.Elab.reuse` message or is the start of the edited top-level
  block, and the number of errors.
- For each script, a file with the script's name followed by
  `-sequences.txt` lists its edit sequences.

The reuse results depend on two things: the edit sequences that the
benchmark sends to the server and the server's behavior. When a reuse
number changes, the sequences files tell which of the two moved. If
the sequences are unchanged, Verso or Lean reuses differently, which
is the change that the benchmark exists to show. If the sequences
changed too, the generator or the derivation of edit sequences
changed, and the difference in reuse may mean nothing.

The test `corpusReuse` replays every script of the corpus in the
language server and compares the reuse with these files. A failure
lists each edit sequence whose results changed, with its reused and
reusable sizes before and after and any other results that changed.
Its last line counts the edit sequences whose missed reuse, the
reusable size minus the reused size, shrank (improved), grew
(regressed) or stayed the same. It ends with the total reused size
before and after. The test `corpusSequences` compares the edit
sequences. Both are run by `lake test` from the repository root. The
test `corpusElaborates` checks that every document of the corpus
elaborates without errors.

## Running the Benchmark

The benchmark's programs, `verso-internal-reuse-bench` and
`verso-internal-edit-scripts`, are in the root Lake config file. They
run a language server in the repository's Lake workspace. To run it,
do the following in the repository root:

```
lake build VersoGen.Genre.Test VersoManual
lake build verso-internal-reuse-bench verso-internal-edit-scripts
lake exe verso-internal-reuse-bench reuse bench/reuse/corpus/minimal-1.json
```

The last command replays one edit script and prints its reuse in the
format of the recorded results. Running
`lake exe verso-internal-reuse-bench` with no arguments prints its
usage, which lists the other commands: printing a document's snapshot
tree, checking the server's answers for a generated document, and
printing how long the server takes to elaborate a file again after an
edit.

## Updating Baseline Results

When a change to Verso or Lean changes the server's reuse,
`corpusReuse` fails, and the results are recorded again after the
difference has been reviewed. From the repository root,
`verso-internal-reuse-bench record` rewrites the reuse file of each
script in `bench/reuse/expected/`:

```
lake exe verso-internal-reuse-bench record
git diff bench/reuse/expected
```

When a change to concretization or to the derivation of edit sequences
changes a `-sequences.txt` file, it should be recorded again from the
repository root with
`lake test -- VersoTests --test-options --update-golden`. This command
rewrites every golden file of the `VersoTests` suite, the benchmark's
reuse files included, so it records the reuse again too.

When a change makes a document of the corpus fail to elaborate, the
corpus is generated again with the arguments in its table. For
example, from the repository root, these commands generate a script of
the `minimal` genre profile from seed 7 with an edit chance of 30, 20
top-level blocks and 4 parts, and write its documents as Lean files:

```
lake exe verso-internal-edit-scripts generate minimal 7 30 /tmp/minimal-7.json --blocks 20 --parts 4
lake exe verso-internal-edit-scripts write /tmp/minimal-7.json /tmp/minimal-7
```
