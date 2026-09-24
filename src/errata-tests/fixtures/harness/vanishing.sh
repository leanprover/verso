#!/usr/bin/env bash
# A test executable that lists one test and then deletes itself, so that the runner cannot start it
# to run the test. The conformance suite runs a copy of it.

if [ "$1" = "errata-list" ]; then
  printf '%s\n' '{"type":"protocol","version":1}' '{"type":"test","name":"gone"}' >> "$2"
  rm -f -- "$0"
  exit 0
fi
exit 0
