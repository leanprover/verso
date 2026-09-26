#!/usr/bin/env bash
# A test executable written in shell, for the conformance suite. Each test shows one way that a test
# executable can end: with or without a verdict, with a verdict that contradicts its exit code, with
# a result file that cannot be read, after a timeout, or by a signal. Its fixtures show the ways a
# fixture's phases can end, and their users stamp a shared file as they run. Invocations chained
# with ';' arguments run in order, each in a subshell, and each value that a setup produces reaches
# the later invocations; after an invocation exits non-zero only teardowns run. A single invocation
# runs in the script's own process.

tests=(pass fail verdict-fail silent unknown-records mismatch-pass mismatch-fail exits sleeps
       stubborn spawns panics garbled records twice flood lingers greets needs-setting protocol-late
       run-id exclusive-a exclusive-b shared-a shared-b after-setup-failure after-prepare-failure-a
       after-prepare-failure-b before-teardown-failure uses-dependent after-slow-setup uses-threaded
       threaded-test fails-with-fixture slow-user slow-named pair-after-failure
       after-missing-setting after-missing-setting-two-away)
# A suite that needs only some of the tests names them here, separated by spaces.
if [ -n "$BASIC_TESTS" ]; then
  read -r -a tests <<< "$BASIC_TESTS"
fi

record() {
  printf '%s\n' "$1" >> "$out"
}

# Every test takes Errata's seed, whose value the runner derives, a marker for the processes it
# starts, and a note, both empty by default. Two tests take more: `greets` a setting with a default,
# and `needs-setting` one that nothing gives a value. The records name the settings as strings,
# except those of `needs-setting` and the fixture `dependent`, which name them in the object form
# with an `optional` field that readers skip.
common='"Errata.seed","marker","note"'

# Performs one invocation and exits with its status.
invoke() {
mode="$1"
out="$2"
case "$mode" in
  errata-list)
    record '{"type":"protocol","version":1}'
    record '{"type":"setting","name":"Errata.seed","description":"The seed."}'
    record '{"type":"setting","name":"marker","description":"Names the processes that a test starts.","default":""}'
    record '{"type":"setting","name":"note","description":"A note.","default":""}'
    record '{"type":"setting","name":"greeting","description":"A greeting.","default":"hello"}'
    record '{"type":"setting","name":"needed","description":"A setting without a default."}'
    record '{"type":"setting","name":"stamp-file","description":"A file that users stamp.","default":""}'
    record '{"type":"fixture","name":"stamped","description":"Its value is the stamp file.","settings":["stamp-file"]}'
    record '{"type":"fixture","name":"setup-fails","description":"Its setup fails."}'
    record '{"type":"fixture","name":"prepare-fails","description":"Its first prepare fails."}'
    record '{"type":"fixture","name":"teardown-fails","description":"Its teardown fails."}'
    record '{"type":"fixture","name":"dependent","settings":[{"name":"greeting","optional":false}],"fixtures":["stamped"]}'
    record '{"type":"fixture","name":"slow-setup","description":"Its setup sleeps."}'
    record '{"type":"fixture","name":"threaded","description":"It asks for threads.","threads":3}'
    record '{"type":"fixture","name":"needs-needed","description":"It takes the setting without a default.","settings":["needed"]}'
    record '{"type":"fixture","name":"on-needs-needed","description":"It takes needs-needed.","fixtures":["needs-needed"]}'
    for t in "${tests[@]}"; do
      settings="$common"
      case "$t" in
        greets) settings="$settings,\"greeting\"" ;;
        needs-setting) settings="$settings,{\"name\":\"needed\",\"optional\":true}" ;;
      esac
      tags='["shell"]'
      case "$t" in
        sleeps|stubborn|flood|lingers) tags='["shell","slow"]' ;;
      esac
      extra=""
      case "$t" in
        exclusive-*|fails-with-fixture|slow-user)
          extra=',"fixtures":[{"name":"stamped","exclusive":true}]' ;;
        shared-*) extra=',"fixtures":[{"name":"stamped","exclusive":false}]' ;;
        after-setup-failure) extra=',"fixtures":[{"name":"setup-fails"}]' ;;
        # Its setups start together when the pool allows, and the first fails.
        pair-after-failure)
          extra=',"fixtures":[{"name":"setup-fails"},{"name":"teardown-fails"}]' ;;
        after-prepare-failure-*) extra=',"fixtures":[{"name":"prepare-fails"}]' ;;
        before-teardown-failure) extra=',"fixtures":[{"name":"teardown-fails"}]' ;;
        uses-dependent) extra=',"fixtures":[{"name":"dependent"}]' ;;
        after-slow-setup) extra=',"fixtures":[{"name":"slow-setup"}]' ;;
        uses-threaded) extra=',"fixtures":[{"name":"threaded"}]' ;;
        after-missing-setting) extra=',"fixtures":[{"name":"needs-needed"}]' ;;
        after-missing-setting-two-away) extra=',"fixtures":[{"name":"on-needs-needed"}]' ;;
        threaded-test) extra=',"threads":3,"fixtures":[{"name":"stamped","exclusive":false}]' ;;
      esac
      record "{\"type\":\"test\",\"name\":\"$t\",\"path\":[\"basic\",\"$t\"],\"file\":\"basic.sh\",\"tags\":$tags,\"settings\":[$settings]$extra}"
    done
    exit 0
    ;;
  errata-fixture)
    name="$3"
    phase="$4"
    shift 4
    stamp_file=""
    value=""
    for arg in "$@"; do
      case "$arg" in
        setting:stamp-file=*) stamp_file="${arg#setting:stamp-file=}" ;;
        "fixture:$name="*) value="${arg#fixture:"$name"=}" ;;
      esac
    done
    record '{"type":"protocol","version":1}'
    # Records the setup's value, and hands it to the chain.
    produce() {
      record "{\"type\":\"value\",\"text\":\"$1\"}"
      if [ -n "$CHAIN_VALUE_FILE" ]; then printf '%s=%s' "$name" "$1" > "$CHAIN_VALUE_FILE"; fi
    }
    case "$name/$phase" in
      stamped/setup)
        [ -n "$stamp_file" ] && echo setup >> "$stamp_file"
        produce "$stamp_file"
        ;;
      stamped/prepare)
        [ -n "$value" ] && echo "prepare start" >> "$value"
        sleep 0.1
        [ -n "$value" ] && echo "prepare end" >> "$value"
        ;;
      stamped/teardown)
        [ -n "$value" ] && echo "teardown" >> "$value"
        ;;
      setup-fails/setup)
        record '{"type":"verdict","status":"fail","message":"the setup failed on request"}'
        exit 1
        ;;
      prepare-fails/setup)
        produce "$(mktemp -d)"
        ;;
      prepare-fails/prepare)
        if [ ! -e "$value/failed-once" ]; then
          : > "$value/failed-once"
          record '{"type":"verdict","status":"fail","message":"the prepare failed on request"}'
          exit 1
        fi
        ;;
      prepare-fails/teardown)
        [ -n "$value" ] && rm -rf "$value"
        ;;
      teardown-fails/teardown)
        record '{"type":"verdict","status":"fail","message":"the teardown failed on request"}'
        exit 1
        ;;
      dependent/setup)
        greeting=""
        stamped=""
        for arg in "$@"; do
          case "$arg" in
            setting:greeting=*) greeting="${arg#setting:greeting=}" ;;
            fixture:stamped=*) stamped="${arg#fixture:stamped=}" ;;
          esac
        done
        produce "$greeting and $stamped"
        ;;
      slow-setup/setup)
        echo "setting up"
        sleep 30
        produce slept
        ;;
      threaded/setup)
        grant=1
        for arg in "$@"; do
          case "$arg" in
            threads:*) grant="${arg#threads:}" ;;
          esac
        done
        echo "threads: $grant; LEAN_NUM_THREADS: ${LEAN_NUM_THREADS:-}"
        produce "$grant"
        ;;
      */setup|*/prepare|*/teardown)
        case "$name" in
          stamped|setup-fails|prepare-fails|teardown-fails|dependent|slow-setup|threaded \
            |needs-needed|on-needs-needed)
            # The teardowns print whether they received their fixture's value.
            [ "$phase" = teardown ] && echo "teardown received ${value:-no value}"
            ;;
          *)
            echo "no fixture is named $name" >&2
            record "{\"type\":\"verdict\",\"status\":\"error\",\"message\":\"no fixture is named $name\"}"
            exit 1
            ;;
        esac
        ;;
      *)
        echo "usage: basic.sh errata-fixture <out> <name> setup|prepare|teardown" >&2
        exit 2
        ;;
    esac
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
      slow-named)
        # A named result that sleeps for 300 ms, and reports that time as its own.
        record '{"type":"protocol","version":1}'
        record '{"type":"result","id":1,"parent":0,"name":"nap"}'
        sleep 0.3
        record '{"type":"result","id":1,"parent":0,"name":"nap","status":"pass","duration_ms":300}'
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
      greets)
        # The settings arrive as arguments, which the test echoes.
        for arg in "$@"; do
          echo "received $arg"
        done
        exit 0
        ;;
      needs-setting)
        echo "ran without its setting"
        exit 0
        ;;
      run-id)
        echo "run id: $ERRATA_RUN_ID"
        grant=""
        for arg in "$@"; do
          case "$arg" in
            threads:*) grant="${arg#threads:}" ;;
          esac
        done
        echo "threads: $grant; LEAN_NUM_THREADS: ${LEAN_NUM_THREADS:-}"
        exit 0
        ;;
      protocol-late)
        record '{"type":"verdict","status":"pass"}'
        record '{"type":"protocol","version":1}'
        exit 0
        ;;
      fails-with-fixture)
        record '{"type":"protocol","version":1}'
        record '{"type":"verdict","status":"fail","message":"it failed with its fixture"}'
        exit 1
        ;;
      slow-user)
        # Stamps the file as it starts, and sleeps past any run that is cancelled meanwhile.
        for arg in "$@"; do
          case "$arg" in
            fixture:stamped=*) echo "start $name" >> "${arg#fixture:stamped=}" ;;
          esac
        done
        sleep 30
        exit 0
        ;;
      exclusive-*|shared-*)
        # Stamps the file that the fixture's value names as it starts and as it ends.
        file=""
        for arg in "$@"; do
          case "$arg" in
            fixture:stamped=*) file="${arg#fixture:stamped=}" ;;
          esac
        done
        [ -n "$file" ] && echo "start $name" >> "$file"
        sleep 0.4
        [ -n "$file" ] && echo "end $name" >> "$file"
        exit 0
        ;;
      after-*|before-*|uses-*)
        # The test prints what it received.
        for arg in "$@"; do
          case "$arg" in
            fixture:*) echo "received $arg" ;;
          esac
        done
        exit 0
        ;;
      threaded-test)
        # Prints its grant, and stamps the file as the users of `stamped` do.
        grant=1
        file=""
        for arg in "$@"; do
          case "$arg" in
            threads:*) grant="${arg#threads:}" ;;
            fixture:stamped=*) file="${arg#fixture:stamped=}" ;;
          esac
        done
        echo "threads: $grant; LEAN_NUM_THREADS: ${LEAN_NUM_THREADS:-}"
        [ -n "$file" ] && echo "start $name" >> "$file"
        sleep 0.4
        [ -n "$file" ] && echo "end $name" >> "$file"
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
    echo "usage: basic.sh errata-list <out> | errata-run <out> <name> [ARG]... |" \
      "errata-fixture <out> <name> <phase> [ARG]..." >&2
    exit 2
    ;;
esac
}

# If there is a single invocation, then it runs in this process, so that tests that ignore a signal
# are the processes that the runner signals.
chained=""
for arg in "$@"; do
  [ "$arg" = ";" ] && chained=1
done
[ -n "$chained" ] || invoke "$@"
failure=""
teardown_failure=""
carried=()
CHAIN_VALUE_FILE=$(mktemp)
while [ $# -gt 0 ]; do
  link=()
  while [ $# -gt 0 ] && [ "$1" != ";" ]; do
    link+=("$1")
    shift
  done
  [ $# -gt 0 ] && shift
  teardown=""
  [ "${link[0]}" = errata-fixture ] && [ "${link[3]:-}" = teardown ] && teardown=1
  # After a link fails, only teardowns run.
  if [ -n "$failure$teardown_failure" ] && [ -z "$teardown" ]; then continue; fi
  case "${link[0]}" in
    errata-run|errata-fixture) link+=(${carried[@]+"${carried[@]}"}) ;;
  esac
  : > "$CHAIN_VALUE_FILE"
  (invoke "${link[@]}")
  status=$?
  if [ -s "$CHAIN_VALUE_FILE" ]; then carried+=("fixture:$(cat "$CHAIN_VALUE_FILE")"); fi
  if [ "$status" -ne 0 ]; then
    if [ -n "$teardown" ]; then
      teardown_failure=${teardown_failure:-$status}
    else
      failure=${failure:-$status}
    fi
  fi
done
rm -f "$CHAIN_VALUE_FILE"
# The first link other than a teardown that failed decides the status, and then a teardown.
exit "${failure:-${teardown_failure:-0}}"
