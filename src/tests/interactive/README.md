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

## Running the tests

The cases are Errata tests with the tag `lsp`, one test per case, named
after the case's file. `lake test` runs them with the rest of Verso's
tests, and a filter selects them alone:

```
lake test -- -E 'tag(lsp)'
lake test -- -E 'exe(interactive) & name(=math_hover)'
```

To run one case by hand, run `./src/tests/interactive/test_single.sh
src/tests/interactive/test-cases/$test_case.lean` from Verso's root
directory.

## Runner architecture

`tests.sh` is the test executable that `errata.toml` adds under the
name `interactive`. It sources Errata's shell harness, declares one test
per file in `test-cases`, and runs a case with the upstream runner.

Files from upstream:

- `run.lean`: main runner
- `test_single.sh`: test a single file
- `common.sh`: diff and miscellaneous testing utilities
