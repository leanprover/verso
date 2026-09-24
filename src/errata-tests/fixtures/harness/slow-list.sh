#!/usr/bin/env bash
# A test executable that takes longer to list its tests than the runner allows.

if [ "$1" = "errata-list" ]; then
  echo "listing slowly"
  sleep 30
fi
exit 0
