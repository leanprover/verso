#!/usr/bin/env bash
# A test executable on Errata's shell harness, for the conformance suite. It declares the tests that
# `basic.sh` writes by hand, with the same behavior, so that each check of the suite runs against a
# script that speaks the protocol by itself and one that the library speaks it for.

source "$ERRATA_DIR/harnesses/errata.sh"

# Declares Errata's seed, which the runner derives, a marker for the processes a test starts, a note,
# a greeting with a default, and a setting without one.
errata_settings() {
  errata_setting_decl Errata.seed "The seed."
  errata_setting_decl marker "Names the processes that a test starts."
  errata_setting_decl note "A note."
  errata_setting_decl greeting "A greeting." --default hello
  errata_setting_decl needed "A setting without a default."
}

# Declares one test per behavior. Every test takes the seed and optionally the marker and the note;
# `greets` also takes the greeting, and `needs-setting` the setting that nothing gives a value.
errata_tests() {
  local t settings tags
  for t in pass fail verdict-fail silent unknown-records mismatch-pass mismatch-fail exits sleeps \
      stubborn spawns panics garbled records twice flood lingers greets needs-setting; do
    settings="Errata.seed,optional(marker),optional(note)"
    case "$t" in
      greets) settings="$settings,greeting" ;;
      needs-setting) settings="$settings,needed" ;;
    esac
    tags=shell
    case "$t" in
      sleeps | stubborn | flood | lingers) tags=shell,slow ;;
    esac
    errata_test "$t" --path "on-errata-sh,$t" --file on-errata-sh.sh --tags "$tags" \
      --settings "$settings"
  done
}

# Runs one test. Each shows one way that a test can end, as the test of the same name in `basic.sh`
# does.
errata_run_test() {
  local marker
  marker=$(errata_setting marker)
  case "$1" in
    pass)
      errata_record '{"type":"verdict","status":"pass"}'
      ;;
    fail)
      echo "failing on purpose"
      exit 1
      ;;
    verdict-fail)
      errata_fail "the check failed"
      ;;
    silent)
      exit 0
      ;;
    unknown-records)
      errata_record '{"type":"mystery","depth":3}'
      errata_record '{"type":"verdict","status":"pass","flavor":"odd"}'
      ;;
    mismatch-pass)
      errata_record '{"type":"verdict","status":"pass"}'
      exit 1
      ;;
    mismatch-fail)
      errata_fail "it failed"
      exit 0
      ;;
    exits)
      echo "about to exit" >&2
      exit 3
      ;;
    sleeps)
      echo "going to sleep"
      sleep 30
      ;;
    stubborn)
      # The signal to terminate is ignored here and by the `sleep` that inherits the disposition, so
      # only the kill ends them.
      trap '' TERM
      echo "ignoring the request to terminate"
      sleep 30
      ;;
    spawns)
      # The background process holds this test's output pipes, and the marker lets the suite find it
      # afterwards. The trailing `:` keeps bash from replacing itself with `sleep`.
      bash -c 'sleep 300; :' "errata-conformance-$marker" &
      exit 0
      ;;
    panics)
      if [ "$LEAN_ABORT_ON_PANIC" = 1 ]; then
        echo "PANIC at the conformance suite" >&2
        kill -ABRT $$
      fi
      ;;
    garbled)
      errata_record 'this is not JSON'
      ;;
    records)
      errata_record '{"type":"output","stream":"stdout","text":"inside\n","result":0}'
      echo "outside"
      errata_record '{"type":"result","id":1,"parent":0,"name":"step"}'
      errata_record '{"type":"result","id":1,"parent":0,"name":"step","status":"pass","duration_ms":1}'
      errata_record '{"type":"verdict","status":"pass"}'
      ;;
    twice)
      errata_fail "first"
      errata_record '{"type":"verdict","status":"pass"}'
      exit 0
      ;;
    flood)
      # Writes records far faster than they can be read, then sleeps past the timeout.
      yes '{"type":"mystery"}' | head -c 200000000 >&9
      sleep 30
      ;;
    lingers)
      # A background process that ignores the request to terminate and holds this test's output
      # pipes, beside a foreground process that ends when asked.
      (trap '' TERM; exec bash -c 'sleep 60; :' "errata-conformance-$marker") &
      trap 'exit 0' TERM
      echo "lingering"
      sleep 60 &
      wait
      ;;
    greets)
      # The test echoes the settings it received, in the order it takes them.
      echo "received setting:Errata.seed=$(errata_setting Errata.seed)"
      echo "received setting:greeting=$(errata_setting greeting)"
      ;;
    needs-setting)
      echo "ran without its setting"
      ;;
  esac
}

errata_main "$@"
