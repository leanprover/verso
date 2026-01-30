#!/usr/bin/env bash
RUN_DIR=src/tests/interactive

source $RUN_DIR/common.sh

# IO.Process.exit (used by the file worker) seems to be incompatible with LSAN
# TODO: investigate or work around
export ASAN_OPTIONS=detect_leaks=0

# these tests don't have to succeed
exec_capture lean -Dlinter.all=false --run "$RUN_DIR/run.lean" -p "$f" || true
diff_produced
