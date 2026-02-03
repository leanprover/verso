# LSP Server Tests for Verso

This directory contains the infrastructure and test cases for Verso
LSP tests.

See
[Lean's LSP testing documentation](https://github.com/leanprover/lean4/blob/master/doc/dev/testing.md#test-suite-organization)
for more information about how to test Lean's LSP server in Verso.

## Adding test cases

To add a test case, add two files to `test-cases` directory:

- A `test.lean` file, with your test case according to the upstream
  documentation.
- A `test.lean.expected.out` that contains the expected test output.
  This can be produced by first creating `test.lean`, running it, and
  verifying that `test.lean.produced.out` has the expected content.
  Then, `test.lean.produced.out` can be copied to
  `test.lean.expected.out` and committed.

## Running individual tests

Do `./src/tests/interactive/run_single.sh $test_case` from Verso's
root directory.

## Runner architecture

The runner architecture lies in a small custom script
`./run_interactive.sh`. This script will call the upstream runner for
each file in `test-cases`. The script is called from the main Verso
test runner, in `src/tests/TestMain.lean`.

Files from upstream:

- `run.lean`: main runner
- `test_single.sh`: test a single file
- `common.sh`: diff and miscellaneous testing utilities
