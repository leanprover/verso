#!/usr/bin/env bash
# A test executable that does not understand the protocol: it prints its inventory to standard
# output instead of writing it to the list file, which it leaves empty.

echo '{"type":"protocol","version":1}'
echo '{"type":"test","name":"lost"}'
exit 0
