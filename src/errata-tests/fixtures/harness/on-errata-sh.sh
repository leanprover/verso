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
  errata_setting_decl stamp-file "A file that users stamp."
}

# Declares one fixture per way that a fixture's phases end, as `basic.sh` does.
errata_fixtures() {
  errata_fixture_decl stamped "Its value is the stamp file." --settings "optional(stamp-file)"
  errata_fixture_decl setup-fails "Its setup fails."
  errata_fixture_decl prepare-fails "Its first prepare fails."
  errata_fixture_decl teardown-fails "Its teardown fails."
  errata_fixture_decl dependent "It joins a greeting and another fixture's value." \
    --settings greeting --fixtures stamped
  errata_fixture_decl slow-setup "Its setup sleeps."
  errata_fixture_decl threaded "It asks for threads." --threads 3
}

# Declares one test per behavior. Every test takes the seed and optionally the marker and the note;
# `greets` also takes the greeting, and `needs-setting` the setting that nothing gives a value. The
# fixtures' users take their fixtures.
errata_tests() {
  local t settings tags extra
  for t in pass fail verdict-fail silent unknown-records mismatch-pass mismatch-fail exits sleeps \
      stubborn spawns panics garbled records twice flood lingers greets needs-setting errexit \
      fail-goes-on run-id exclusive-a exclusive-b shared-a shared-b after-setup-failure \
      after-prepare-failure-a after-prepare-failure-b before-teardown-failure uses-dependent \
      after-slow-setup uses-threaded threaded-test; do
    settings="Errata.seed,optional(marker),optional(note)"
    case "$t" in
      greets) settings="$settings,greeting" ;;
      needs-setting) settings="$settings,needed" ;;
    esac
    tags=shell
    case "$t" in
      sleeps | stubborn | flood | lingers) tags=shell,slow ;;
    esac
    extra=()
    case "$t" in
      exclusive-*) extra=(--fixtures stamped) ;;
      shared-*) extra=(--fixtures "shared(stamped)") ;;
      after-setup-failure) extra=(--fixtures setup-fails) ;;
      after-prepare-failure-*) extra=(--fixtures prepare-fails) ;;
      before-teardown-failure) extra=(--fixtures teardown-fails) ;;
      uses-dependent) extra=(--fixtures dependent) ;;
      after-slow-setup) extra=(--fixtures slow-setup) ;;
      uses-threaded) extra=(--fixtures threaded) ;;
      threaded-test) extra=(--threads 3 --fixtures "shared(stamped)") ;;
    esac
    errata_test "$t" --path "on-errata-sh,$t" --file on-errata-sh.sh --tags "$tags" \
      --settings "$settings" ${extra[@]+"${extra[@]}"}
  done
}

# Runs one phase of a fixture, as the fixture of the same name in `basic.sh` does. The teardowns of
# the fixtures other than `stamped` print whether they received their value.
errata_fixture_setup() {
  case "$1" in
    stamped)
      local file
      file=$(errata_setting stamp-file) || file=""
      if [ -n "$file" ]; then echo setup >> "$file"; fi
      errata_value "$file"
      ;;
    setup-fails) errata_fail "the setup failed on request" ;;
    prepare-fails) errata_value "$(mktemp -d)" ;;
    dependent) errata_value "$(errata_setting greeting) and $(errata_fixture_value stamped)" ;;
    slow-setup)
      echo "setting up"
      sleep 30
      errata_value slept
      ;;
    threaded)
      echo "threads: $(errata_threads); LEAN_NUM_THREADS: ${LEAN_NUM_THREADS:-}"
      errata_value "$(errata_threads)"
      ;;
  esac
}

errata_fixture_prepare() {
  local value
  value=$(errata_fixture_value "$1") || value=""
  case "$1" in
    stamped)
      if [ -n "$value" ]; then echo "prepare start" >> "$value"; fi
      sleep 0.1
      if [ -n "$value" ]; then echo "prepare end" >> "$value"; fi
      ;;
    prepare-fails)
      if [ ! -e "$value/failed-once" ]; then
        : > "$value/failed-once"
        errata_fail "the prepare failed on request"
      fi
      ;;
  esac
}

errata_fixture_teardown() {
  local value
  if value=$(errata_fixture_value "$1"); then :; else value=""; fi
  case "$1" in
    stamped) if [ -n "$value" ]; then echo teardown >> "$value"; fi ;;
    prepare-fails) if [ -n "$value" ]; then rm -rf "$value"; fi ;;
    teardown-fails) errata_fail "the teardown failed on request" ;;
    *) echo "teardown received ${value:-no value}" ;;
  esac
}

# Runs one test. Each shows one way that a test can end, as the test of the same name in `basic.sh`
# does; `errexit` and `fail-goes-on` show how the harness ends a test that fails.
errata_run_test() {
  local marker
  marker=$(errata_setting marker) || true
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
      # The harness exits with 1 after `errata_fail`, so this test fails where `basic.sh`'s
      # contradicts its verdict.
      errata_fail "it failed" || true
      exit 0
      ;;
    run-id)
      echo "run id: ${ERRATA_RUN_ID:-}"
      ;;
    errexit)
      false
      echo "REACHED after false"
      ;;
    fail-goes-on)
      errata_fail "stopped here" || true
      echo "went on"
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
      errata_fail "first" || true
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
    exclusive-* | shared-* | threaded-test)
      # Stamps the file that the fixture's value names as it starts and as it ends; the test that
      # asks for threads also prints its grant.
      if [ "$1" = threaded-test ]; then
        echo "threads: $(errata_threads); LEAN_NUM_THREADS: ${LEAN_NUM_THREADS:-}"
      fi
      local file
      file=$(errata_fixture_value stamped) || file=""
      if [ -n "$file" ]; then echo "start $1" >> "$file"; fi
      sleep 0.4
      if [ -n "$file" ]; then echo "end $1" >> "$file"; fi
      ;;
    after-* | before-* | uses-*)
      local f
      for f in stamped setup-fails prepare-fails teardown-fails dependent slow-setup threaded; do
        if errata_fixture_value "$f" > /dev/null; then
          echo "received fixture:$f=$(errata_fixture_value "$f")"
        fi
      done
      ;;
  esac
}

errata_main "$@"
