#!/usr/bin/env bash
# A test executable that lists its one test and leaves behind a process in a session of its own,
# which holds its output pipes open. The process carries the marker from `MARKER` so that the suite
# can end it afterwards.

if [ "$1" = "errata-list" ]; then
  printf '%s\n' '{"type":"protocol","version":1}' '{"type":"test","name":"listed"}' >> "$2"
  if command -v setsid > /dev/null; then
    setsid bash -c 'sleep 20; :' "errata-conformance-$MARKER" &
  else
    perl -MPOSIX -e 'POSIX::setsid(); exec "bash", "-c", "sleep 20; :", $ARGV[0]' \
      "errata-conformance-$MARKER" &
  fi
  exit 0
fi
exit 0
