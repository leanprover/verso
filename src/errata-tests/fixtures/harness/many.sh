#!/usr/bin/env bash
# A test executable on Errata's shell harness with many trivial tests, for the checks of how many
# files the runner holds open over a run. `ERRATA_MANY` sets the number of tests, 300 when unset.

source "$ERRATA_DIR/harnesses/errata.sh"

errata_tests() {
  local i
  for ((i = 0; i < ${ERRATA_MANY:-300}; i++)); do
    errata_test "t$i"
  done
}

errata_run_test() {
  :
}

errata_main "$@"
