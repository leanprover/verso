#!/usr/bin/env bash
# Verso's language server tests as an Errata test executable on Errata's shell harness: one test per
# case in `test-cases`, each run by `test_single.sh`, which compares what the language server answers
# with the case's expected output. The runner starts it from the repository's root.

source "$ERRATA_DIR/harnesses/errata.sh"

cases=src/tests/interactive/test-cases

# Declares one test per case, named after the case's file.
errata_tests() {
  local f name
  for f in "$cases"/*.lean; do
    name=$(basename "$f" .lean)
    errata_test "$name" --path "interactive,$name" --file "$f" --line 1 --tags lsp \
      --description "The language server's answers for $name.lean match $name.lean.expected.out."
  done
}

# Runs one case. Its output streams to the test's output as it arrives and is also kept, so that a
# failure's verdict can carry it as its detail.
errata_run_test() {
  local log status output
  log=$(mktemp)
  set -o pipefail
  if src/tests/interactive/test_single.sh "$cases/$1.lean" 2>&1 | tee "$log"; then
    status=0
  else
    status=$?
  fi
  output=$(cat "$log")
  rm -f "$log"
  if [ "$status" -ne 0 ]; then
    errata_fail "test_single.sh failed on $1.lean with exit code $status" "$output"
  fi
}

errata_main "$@"
