#!/usr/bin/env bash
# Errata's shell harness: a bash library that a script sources to become an Errata test executable.
# The library speaks the test-executable protocol, and the script says what its tests are and how to
# run one. Scripts look like this:
#
#   source "$ERRATA_DIR/harnesses/errata.sh"
#
#   errata_settings() {
#     errata_setting_decl greeting "The word to greet with." --default hello
#   }
#
#   errata_fixtures() {
#     errata_fixture_decl workdir "A directory that the tests share." --settings greeting
#   }
#
#   errata_tests() {
#     errata_test greets --path "demo,greets" --tags quick --settings greeting --fixtures workdir
#   }
#
#   errata_fixture_setup() {
#     case "$1" in
#       workdir) errata_value "$(mktemp -d)" ;;
#     esac
#   }
#
#   errata_fixture_teardown() {
#     case "$1" in
#       workdir) if dir=$(errata_fixture_value workdir); then rm -rf "$dir"; fi ;;
#     esac
#   }
#
#   errata_run_test() {
#     case "$1" in
#       greets) [ "$(errata_setting greeting)" = hello ] || errata_fail "an unexpected greeting" ;;
#     esac
#   }
#
#   errata_main "$@"
#
# Tests' bodies run in subshells with `set -e`: commands that fail end the test with their status.
# `errata_fail` writes a failing verdict and returns 1, which ends the body unless the body catches
# the status; the test fails either way. Fixtures' phases run the same way, through
# `errata_fixture_setup`, `errata_fixture_prepare`, and `errata_fixture_teardown`, each given the
# fixture's name; a script without a prepare or a teardown function has nothing to do in that phase.
#
# The runner sets three variables in every test executable's environment: ERRATA_DIR, the directory
# of Errata's sources; ERRATA_RUN_ID, the run's identifier, the same for every process of one run and
# different in the next, for work a script does once per run; and ERRATA_LIFELINE=1, which marks
# standard input as a pipe that closes when the runner ends. Scripts read the first two from their
# environment, and the runner ends shell tests' process groups itself. A test or fixture that asks
# for threads also receives LEAN_NUM_THREADS, the same number as `errata_threads` prints.
#
# The library needs bash 3.2 or later and the POSIX utilities that ship with macOS and Linux. It
# writes the records to file descriptor 9, which it opens on the file that the runner names, so the
# script's own standard output and standard error stay free for the test's output.

# The declared settings' names and defaults, and the fixtures' and tests' names, as errata-run and
# errata-fixture collect them.
_errata_setting_names=()
_errata_setting_defaults=()
_errata_fixture_names=()
_errata_test_names=()
# The settings and the fixtures' values that an invocation receives, as parallel arrays of names
# and values.
_errata_given_names=()
_errata_given_values=()
_errata_given_fixture_names=()
_errata_given_fixture_values=()
# The thread grant that an invocation receives, empty when it receives none.
_errata_threads=""
# `list` while errata-list writes the inventory, and `collect` while an invocation learns the names.
_errata_mode=""
# What errata-list has written so far: `fixture` after a fixture record, and `test` after a test
# record. Settings precede fixtures, which precede tests.
_errata_listed=""
# The file that errata_fail creates while a test runs, so that the harness learns of the failure.
_errata_failed_mark=""
# The file that errata_value writes the value to while a setup runs.
_errata_value_mark=""
# The fixture and the value that the last setup of a chain produced, for the invocations after it.
_errata_produced_fixture=""
_errata_produced_value=""

# The control characters that JSON strings escape as \u00XX, apart from tab, newline, and carriage
# return, which have short escapes, and the escape of each.
_errata_control_chars=()
_errata_control_escapes=()
for _errata_code in 1 2 3 4 5 6 7 8 11 12 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 127; do
  printf -v _errata_octal '%03o' "$_errata_code"
  # shellcheck disable=SC2059 # The format is the octal escape of the character.
  printf -v _errata_char "\\$_errata_octal"
  _errata_control_chars+=("$_errata_char")
  printf -v _errata_char '\\u%04x' "$_errata_code"
  _errata_control_escapes+=("$_errata_char")
done
unset _errata_code _errata_octal _errata_char

# The helpers below leave the JSON they make in this variable, so that the library builds records
# without starting a subshell for each field.
_errata_json=""

# Makes its argument a JSON string, quotes included.
_errata_json_string() {
  local s=$1 i
  s=${s//\\/\\\\}
  s=${s//\"/\\\"}
  s=${s//$'\n'/\\n}
  s=${s//$'\r'/\\r}
  s=${s//$'\t'/\\t}
  if [[ $s == *[[:cntrl:]]* ]]; then
    for i in "${!_errata_control_chars[@]}"; do
      s=${s//"${_errata_control_chars[$i]}"/"${_errata_control_escapes[$i]}"}
    done
  fi
  _errata_json="\"$s\""
}

# Makes a comma-separated list a JSON array of strings.
_errata_json_list() {
  local items=() item out="" sep=""
  IFS=',' read -r -a items <<< "$1"
  for item in ${items[@]+"${items[@]}"}; do
    _errata_json_string "$item"
    out+="$sep$_errata_json"
    sep=","
  done
  _errata_json="[$out]"
}

# Makes a comma-separated list of settings, each a name or `optional(name)`, the JSON array of a
# record's `settings` field.
_errata_json_settings() {
  local items=() item out="" sep="" name optional
  IFS=',' read -r -a items <<< "$1"
  for item in ${items[@]+"${items[@]}"}; do
    case "$item" in
      "optional("*")")
        name=${item#optional(}
        name=${name%)}
        optional=true
        ;;
      *)
        name=$item
        optional=false
        ;;
    esac
    _errata_json_string "$name"
    out+="$sep{\"name\":$_errata_json,\"optional\":$optional}"
    sep=","
  done
  _errata_json="[$out]"
}

# Makes a comma-separated list of fixtures, each a name or `shared(name)`, the JSON array of a test
# record's `fixtures` field.
_errata_json_fixtures() {
  local items=() item out="" sep="" name exclusive
  IFS=',' read -r -a items <<< "$1"
  for item in ${items[@]+"${items[@]}"}; do
    case "$item" in
      "shared("*")")
        name=${item#shared(}
        name=${name%)}
        exclusive=false
        ;;
      *)
        name=$item
        exclusive=true
        ;;
    esac
    _errata_json_string "$name"
    out+="$sep{\"name\":$_errata_json,\"exclusive\":$exclusive}"
    sep=","
  done
  _errata_json="[$out]"
}

# Reports a mistake in how the script uses the library, and ends the process with 2.
_errata_misuse() {
  printf 'errata.sh: %s\n' "$1" >&2
  exit 2
}

# Checks that an option's value is a whole number.
_errata_require_number() {
  case "$2" in
    '' | *[!0-9]*) _errata_misuse "$1 takes a whole number, and it was given '$2'" ;;
  esac
}

# Writes one record, a line of JSON, to the file that the runner named. The library's own functions
# write every record the protocol defines; this one is for anything else.
errata_record() {
  printf '%s\n' "$1" >&9
}

# Declares a setting that the script's tests take: `errata_setting_decl NAME DESCRIPTION
# [--default VALUE]`. The script calls it from `errata_settings`.
errata_setting_decl() {
  [ $# -ge 2 ] || _errata_misuse "errata_setting_decl takes a name and a description"
  local name=$1 description=$2 default="" has_default=""
  shift 2
  while [ $# -gt 0 ]; do
    case "$1" in
      --default)
        [ $# -ge 2 ] || _errata_misuse "--default takes a value"
        default=$2
        has_default=1
        shift 2
        ;;
      *) _errata_misuse "errata_setting_decl has no option $1" ;;
    esac
  done
  case "$_errata_mode" in
    list)
      [ -z "$_errata_listed" ] || _errata_misuse "the setting $name is declared after a \
$_errata_listed; declare settings in errata_settings"
      local record
      _errata_json_string "$name"
      record="{\"type\":\"setting\",\"name\":$_errata_json"
      _errata_json_string "$description"
      record+=",\"description\":$_errata_json"
      if [ -n "$has_default" ]; then
        _errata_json_string "$default"
        record+=",\"default\":$_errata_json"
      fi
      errata_record "$record}"
      ;;
    collect)
      if [ -n "$has_default" ]; then
        _errata_setting_names+=("$name")
        _errata_setting_defaults+=("$default")
      fi
      ;;
  esac
}

# Declares a fixture: `errata_fixture_decl NAME DESCRIPTION [--settings a,optional(b)]
# [--fixtures c,d] [--threads N]`. Its fixtures are ones declared before it. The script calls it
# from `errata_fixtures`.
errata_fixture_decl() {
  [ $# -ge 2 ] || _errata_misuse "errata_fixture_decl takes a name and a description"
  local name=$1 description=$2
  shift 2
  # Collecting needs only the name.
  if [ "$_errata_mode" = collect ]; then
    _errata_fixture_names+=("$name")
    return 0
  fi
  local record
  _errata_json_string "$name"
  record="{\"type\":\"fixture\",\"name\":$_errata_json"
  _errata_json_string "$description"
  record+=",\"description\":$_errata_json"
  while [ $# -gt 0 ]; do
    [ $# -ge 2 ] || _errata_misuse "$1 takes a value"
    case "$1" in
      --settings | --fixtures)
        case "$2" in
          *$'\n'*) _errata_misuse "the value of $1 for the fixture $name holds a newline" ;;
        esac
        ;;
    esac
    case "$1" in
      --settings)
        _errata_json_settings "$2"
        record+=",\"settings\":$_errata_json"
        ;;
      --fixtures)
        _errata_json_list "$2"
        record+=",\"fixtures\":$_errata_json"
        ;;
      --threads)
        _errata_require_number --threads "$2"
        record+=",\"threads\":$2"
        ;;
      *) _errata_misuse "errata_fixture_decl has no option $1" ;;
    esac
    shift 2
  done
  if [ "$_errata_mode" = list ]; then
    [ "$_errata_listed" != test ] || _errata_misuse "the fixture $name is declared after a test; \
declare fixtures in errata_fixtures"
    errata_record "$record}"
    _errata_listed="fixture"
  fi
}

# Declares a test: `errata_test NAME [--path a,b,c] [--file F] [--line N] [--description TEXT]
# [--tags a,b] [--settings a,optional(b)] [--fixtures c,shared(d)] [--threads N]`. Settings written
# `optional(b)` are ones the tests run without, and fixtures written `shared(d)` are ones the tests
# share with other shared users; the others they use alone. The script calls it from
# `errata_tests`.
errata_test() {
  [ $# -ge 1 ] || _errata_misuse "errata_test takes a name"
  local name=$1
  shift
  # Collecting needs only the name.
  if [ "$_errata_mode" = collect ]; then
    _errata_test_names+=("$name")
    return 0
  fi
  local record
  _errata_json_string "$name"
  record="{\"type\":\"test\",\"name\":$_errata_json"
  while [ $# -gt 0 ]; do
    [ $# -ge 2 ] || _errata_misuse "$1 takes a value"
    case "$1" in
      --path | --tags | --settings | --fixtures)
        case "$2" in
          *$'\n'*) _errata_misuse "the value of $1 for the test $name holds a newline" ;;
        esac
        ;;
    esac
    case "$1" in
      --path | --tags) _errata_json_list "$2" ;;
      --file | --description) _errata_json_string "$2" ;;
      --settings) _errata_json_settings "$2" ;;
      --fixtures) _errata_json_fixtures "$2" ;;
      --line | --threads)
        _errata_require_number "$1" "$2"
        _errata_json=$2
        ;;
      *) _errata_misuse "errata_test has no option $1" ;;
    esac
    record+=",\"${1#--}\":$_errata_json"
    shift 2
  done
  if [ "$_errata_mode" = list ]; then
    errata_record "$record}"
    _errata_listed="test"
  fi
}

# Prints the value of a setting that the test received, or else its declared default. The status is
# 1 when the setting has neither.
errata_setting() {
  local i
  # The expansions stay valid for an empty array under `set -u` in every version of bash.
  for i in ${_errata_given_names[@]+"${!_errata_given_names[@]}"}; do
    if [ "${_errata_given_names[$i]}" = "$1" ]; then
      printf '%s' "${_errata_given_values[$i]}"
      return 0
    fi
  done
  for i in ${_errata_setting_names[@]+"${!_errata_setting_names[@]}"}; do
    if [ "${_errata_setting_names[$i]}" = "$1" ]; then
      printf '%s' "${_errata_setting_defaults[$i]}"
      return 0
    fi
  done
  return 1
}

# Prints the value of a fixture that the test or fixture phase received. The status is 1 when it
# received none, as a teardown does after a setup that failed.
errata_fixture_value() {
  local i found="" given=""
  for i in ${_errata_given_fixture_names[@]+"${!_errata_given_fixture_names[@]}"}; do
    # The last value given for a name counts.
    if [ "${_errata_given_fixture_names[$i]}" = "$1" ]; then
      found=${_errata_given_fixture_values[$i]}
      given=1
    fi
  done
  [ -n "$given" ] || return 1
  printf '%s' "$found"
}

# Prints the number of hardware threads that the runner granted the test or fixture phase, 1 when it
# granted none.
errata_threads() {
  printf '%s' "${_errata_threads:-1}"
}

# Gives the fixture whose setup is running its value: `errata_value TEXT` writes the value record.
errata_value() {
  _errata_json_string "$1"
  errata_record "{\"type\":\"value\",\"text\":$_errata_json}"
  if [ -n "$_errata_value_mark" ]; then printf '%s' "$1" > "$_errata_value_mark"; fi
}

# Fails the test: `errata_fail MESSAGE [DETAIL]` writes a verdict with the message and the detail,
# and returns 1.
errata_fail() {
  local record
  _errata_json_string "$1"
  record="{\"type\":\"verdict\",\"status\":\"fail\",\"message\":$_errata_json"
  if [ $# -ge 2 ]; then
    _errata_json_string "$2"
    record+=",\"detail\":$_errata_json"
  fi
  errata_record "$record}"
  if [ -n "$_errata_failed_mark" ]; then : > "$_errata_failed_mark"; fi
  return 1
}

# Prints the usage of a test executable.
_errata_usage() {
  cat >&2 <<EOF
usage:
  $0 errata-list <out>
  $0 errata-run <out> <test-name> [setting:NAME=VALUE]... [fixture:NAME=VALUE]... [threads:N]
  $0 errata-fixture <out> <fixture-name> setup|prepare|teardown [setting:NAME=VALUE]...
      [fixture:NAME=VALUE]... [threads:N]

Several invocations may be chained, each separated by a ';' argument. The Errata runner starts test
executables; to run the tests, run the Errata driver, which is usually \`lake test\`.
EOF
}

# The current time in milliseconds since the Unix epoch, to the second where bash has no finer clock.
_errata_now_ms() {
  if [ -n "${EPOCHREALTIME:-}" ]; then
    local t=${EPOCHREALTIME/[^0-9]/}
    printf '%s' "${t:0:${#t}-3}"
  else
    printf '%s000' "$(date +%s)"
  fi
}

# Whether the first argument is among the rest.
_errata_among() {
  local wanted=$1 item
  shift
  for item in "$@"; do
    [ "$item" = "$wanted" ] && return 0
  done
  return 1
}

# Takes in an invocation's arguments after the name: each `setting:NAME=VALUE`, each
# `fixture:NAME=VALUE`, and `threads:N`.
_errata_take_args() {
  local arg pair
  _errata_given_names=()
  _errata_given_values=()
  _errata_given_fixture_names=()
  _errata_given_fixture_values=()
  _errata_threads=""
  for arg in "$@"; do
    case "$arg" in
      setting:* | fixture:*)
        pair=${arg#*:}
        case "$arg" in
          setting:*) _errata_given_names+=("${pair%%=*}") ;;
          fixture:*) _errata_given_fixture_names+=("${pair%%=*}") ;;
        esac
        case "$pair" in
          *=*) pair=${pair#*=} ;;
          *) pair="" ;;
        esac
        case "$arg" in
          setting:*) _errata_given_values+=("$pair") ;;
          fixture:*) _errata_given_fixture_values+=("$pair") ;;
        esac
        ;;
      threads:*) _errata_threads=${arg#threads:} ;;
    esac
  done
}

# Learns the declared settings' defaults and the fixtures' and tests' names, by calling the script's
# declaring functions in the collecting mode.
_errata_collect() {
  _errata_setting_names=()
  _errata_setting_defaults=()
  _errata_fixture_names=()
  _errata_test_names=()
  _errata_mode=collect
  if declare -F errata_settings > /dev/null; then errata_settings; fi
  if declare -F errata_fixtures > /dev/null; then errata_fixtures; fi
  if declare -F errata_tests > /dev/null; then errata_tests; fi
  _errata_mode=""
}

# Runs a body, the function named by its first argument with the rest as arguments, in a subshell
# with `set -e`, and returns its status, or 1 when it called `errata_fail`. The body's value, from
# `errata_value`, is left in `_errata_produced_value`.
_errata_run_body() {
  local errexit="" marks status
  marks=$(mktemp -d)
  _errata_failed_mark="$marks/failed"
  _errata_value_mark="$marks/value"
  case $- in *e*) errexit=1 ;; esac
  # The body runs in a subshell, so that its `exit` ends only the body, and with `errexit`, so that
  # a failing command ends it. Bash honors `errexit` only in a subshell that is a command of its
  # own, outside any condition.
  set +e
  (set -e; "$@")
  status=$?
  [ -n "$errexit" ] && set -e
  # Bodies that failed with `errata_fail` exit with 1, whatever they returned.
  [ -e "$_errata_failed_mark" ] && status=1
  _errata_produced_value=""
  [ -e "$_errata_value_mark" ] && _errata_produced_value=$(cat "$_errata_value_mark"; printf x)
  _errata_produced_value=${_errata_produced_value%x}
  rm -rf "$marks"
  _errata_failed_mark=""
  _errata_value_mark=""
  return "$status"
}

# Writes an error verdict with the message to the output file and to standard error.
_errata_error() {
  printf '%s\n' "$1" >&2
  _errata_json_string "$1"
  errata_record "{\"type\":\"verdict\",\"status\":\"error\",\"message\":$_errata_json}"
}

# Performs one invocation, and returns its exit status. A setup that succeeds leaves its fixture's
# name and value in `_errata_produced_fixture` and `_errata_produced_value`.
_errata_invoke() {
  _errata_produced_fixture=""
  case "${1:-}" in
    errata-list)
      [ $# -eq 2 ] || { _errata_usage; return 2; }
      exec 9>>"$2"
      errata_record '{"type":"protocol","version":1}'
      _errata_mode=list
      _errata_listed=""
      if declare -F errata_settings > /dev/null; then errata_settings; fi
      if declare -F errata_fixtures > /dev/null; then errata_fixtures; fi
      if declare -F errata_tests > /dev/null; then errata_tests; fi
      _errata_mode=""
      exec 9>&-
      return 0
      ;;
    errata-run)
      [ $# -ge 3 ] || { _errata_usage; return 2; }
      local out=$2 name=$3 status
      shift 3
      _errata_take_args "$@"
      exec 9>>"$out"
      errata_record '{"type":"protocol","version":1}'
      _errata_collect
      if ! _errata_among "$name" ${_errata_test_names[@]+"${_errata_test_names[@]}"}; then
        _errata_error "no test is named $name"
        exec 9>&-
        return 1
      fi
      declare -F errata_run_test > /dev/null ||
        _errata_misuse "the script declares tests and defines no errata_run_test"
      errata_record "{\"type\":\"start\",\"time_ms\":$(_errata_now_ms)}"
      _errata_run_body errata_run_test "$name"
      status=$?
      exec 9>&-
      return "$status"
      ;;
    errata-fixture)
      [ $# -ge 4 ] || { _errata_usage; return 2; }
      local out=$2 name=$3 phase=$4 status
      case "$phase" in
        setup | prepare | teardown) ;;
        *) _errata_usage; return 2 ;;
      esac
      shift 4
      _errata_take_args "$@"
      exec 9>>"$out"
      errata_record '{"type":"protocol","version":1}'
      _errata_collect
      if ! _errata_among "$name" ${_errata_fixture_names[@]+"${_errata_fixture_names[@]}"}; then
        _errata_error "no fixture is named $name"
        exec 9>&-
        return 1
      fi
      if ! declare -F "errata_fixture_$phase" > /dev/null; then
        status=0
        # Prepares and teardowns without a function have nothing to do; a setup needs one.
        if [ "$phase" = setup ]; then
          _errata_error "the script declares fixtures and defines no errata_fixture_setup"
          status=1
        fi
        exec 9>&-
        return "$status"
      fi
      _errata_run_body "errata_fixture_$phase" "$name"
      status=$?
      exec 9>&-
      if [ "$status" -eq 0 ] && [ "$phase" = setup ]; then _errata_produced_fixture=$name; fi
      return "$status"
      ;;
    *)
      _errata_usage
      return 2
      ;;
  esac
}

# The main of a test executable. It performs the invocation that its arguments give, or each
# invocation of a chain whose invocations are separated by a ';' argument, in order. Each value that
# a setup produces is added to the later errata-run and errata-fixture invocations as that fixture's
# `fixture:NAME=VALUE` argument, and after an invocation exits non-zero only teardowns run. It exits
# with the status of the first invocation other than a teardown that exited non-zero, or else with
# that of the first teardown that did, or else 0. `errata-list` writes the inventory: the
# settings that `errata_settings` declares, then the fixtures that `errata_fixtures` declares, then
# the tests that `errata_tests` declares. `errata-run` runs one test with `errata_run_test NAME`,
# and `errata-fixture` one phase of a fixture with `errata_fixture_PHASE NAME`, each in a subshell
# with `set -e`, so that a command that fails ends it, and exits with its status, or with 1 when it
# called `errata_fail`.
errata_main() {
  local status invocation carried=() failure="" teardown_failure="" teardown
  [ $# -gt 0 ] || { _errata_usage; exit 2; }
  while [ $# -gt 0 ]; do
    invocation=()
    while [ $# -gt 0 ] && [ "$1" != ";" ]; do
      invocation+=("$1")
      shift
    done
    [ $# -gt 0 ] && shift
    teardown=""
    if [ "${invocation[0]:-}" = errata-fixture ] && [ "${invocation[3]:-}" = teardown ]; then
      teardown=1
    fi
    if [ -n "$failure$teardown_failure" ] && [ -z "$teardown" ]; then continue; fi
    case "${invocation[0]:-}" in
      errata-run | errata-fixture) invocation+=(${carried[@]+"${carried[@]}"}) ;;
    esac
    # The invocation is a command of its own, outside any condition, so that the body's `errexit`
    # takes effect.
    set +e
    _errata_invoke ${invocation[@]+"${invocation[@]}"}
    status=$?
    if [ -n "$_errata_produced_fixture" ]; then
      carried+=("fixture:$_errata_produced_fixture=$_errata_produced_value")
    fi
    if [ "$status" -ne 0 ]; then
      if [ -n "$teardown" ]; then
        teardown_failure=${teardown_failure:-$status}
      else
        failure=${failure:-$status}
      fi
    fi
  done
  exit "${failure:-${teardown_failure:-0}}"
}
