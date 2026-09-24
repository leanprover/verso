#!/usr/bin/env bash
# A test executable written in shell, for the conformance suite. Each test shows one way that a test
# executable can end: with or without a verdict, with a verdict that contradicts its exit code, with
# a result file that cannot be read, after a timeout, or by a signal.

mode="$1"
out="$2"

tests=(pass fail verdict-fail silent unknown-records mismatch-pass mismatch-fail exits sleeps
       stubborn spawns panics garbled records twice flood lingers)
# A suite that needs only some of the tests names them here, separated by spaces.
if [ -n "$BASIC_TESTS" ]; then
  read -r -a tests <<< "$BASIC_TESTS"
fi

record() {
  printf '%s\n' "$1" >> "$out"
}

case "$mode" in
  errata-list)
    record '{"type":"protocol","version":1}'
    for t in "${tests[@]}"; do
      record "{\"type\":\"test\",\"name\":\"$t\",\"path\":[\"basic\",\"$t\"],\"file\":\"basic.sh\"}"
    done
    exit 0
    ;;
  errata-run)
    name="$3"
    shift 3
    marker=""
    for arg in "$@"; do
      case "$arg" in
        setting:marker=*) marker="${arg#setting:marker=}" ;;
      esac
    done
    case "$name" in
      pass)
        record '{"type":"protocol","version":1}'
        record '{"type":"start"}'
        record '{"type":"verdict","status":"pass"}'
        exit 0
        ;;
      fail)
        echo "failing on purpose"
        exit 1
        ;;
      verdict-fail)
        record '{"type":"protocol","version":1}'
        record '{"type":"verdict","status":"fail","message":"the check failed"}'
        exit 1
        ;;
      silent)
        exit 0
        ;;
      unknown-records)
        record '{"type":"protocol","version":1}'
        record '{"type":"mystery","depth":3}'
        record '{"type":"verdict","status":"pass","flavor":"odd"}'
        exit 0
        ;;
      mismatch-pass)
        record '{"type":"protocol","version":1}'
        record '{"type":"verdict","status":"pass"}'
        exit 1
        ;;
      mismatch-fail)
        record '{"type":"protocol","version":1}'
        record '{"type":"verdict","status":"fail","message":"it failed"}'
        exit 0
        ;;
      exits)
        echo "about to exit" >&2
        exit 3
        ;;
      sleeps)
        echo "going to sleep"
        sleep 30
        exit 0
        ;;
      stubborn)
        # The signal to terminate is ignored here and by the `sleep` that inherits the disposition,
        # so only the kill ends them.
        trap '' TERM
        echo "ignoring the request to terminate"
        sleep 30
        exit 0
        ;;
      spawns)
        # The background process holds this test's output pipes, and the marker lets the suite find
        # it afterwards. The trailing `:` keeps bash from replacing itself with `sleep`.
        bash -c 'sleep 300; :' "errata-conformance-$marker" &
        exit 0
        ;;
      panics)
        if [ "$LEAN_ABORT_ON_PANIC" = 1 ]; then
          echo "PANIC at the conformance suite" >&2
          kill -ABRT $$
        fi
        exit 0
        ;;
      garbled)
        record '{"type":"protocol","version":1}'
        record 'this is not JSON'
        exit 0
        ;;
      records)
        record '{"type":"protocol","version":1}'
        record '{"type":"start","time_ms":1}'
        record '{"type":"output","stream":"stdout","text":"inside\n","result":0}'
        echo "outside"
        record '{"type":"result","id":1,"parent":0,"name":"step"}'
        record '{"type":"result","id":1,"parent":0,"name":"step","status":"pass","duration_ms":1}'
        record '{"type":"verdict","status":"pass"}'
        exit 0
        ;;
      twice)
        record '{"type":"protocol","version":1}'
        record '{"type":"verdict","status":"fail","message":"first"}'
        record '{"type":"verdict","status":"pass"}'
        exit 0
        ;;
      flood)
        # Writes records far faster than they can be read, then sleeps past the timeout.
        record '{"type":"protocol","version":1}'
        yes '{"type":"mystery"}' | head -c 200000000 >> "$out"
        sleep 30
        exit 0
        ;;
      lingers)
        # A background process that ignores the request to terminate and holds this test's output
        # pipes, beside a foreground process that ends when asked.
        (trap '' TERM; exec bash -c 'sleep 60; :' "errata-conformance-$marker") &
        trap 'exit 0' TERM
        echo "lingering"
        sleep 60 &
        wait
        exit 0
        ;;
      *)
        record '{"type":"protocol","version":1}'
        record "{\"type\":\"verdict\",\"status\":\"error\",\"message\":\"no test is named $name\"}"
        exit 1
        ;;
    esac
    ;;
  *)
    echo "usage: basic.sh errata-list <out> | errata-run <out> <name> [setting:K=V]..." >&2
    exit 2
    ;;
esac
