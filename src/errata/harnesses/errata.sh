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
#   errata_tests() {
#     errata_test greets --path "demo,greets" --tags quick --settings greeting
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
# the status; the test fails either way.
#
# The runner sets three variables in every test executable's environment: ERRATA_DIR, the directory
# of Errata's sources; ERRATA_RUN_ID, the run's identifier, the same for every process of one run and
# different in the next, for work a script does once per run; and ERRATA_LIFELINE=1, which marks
# standard input as a pipe that closes when the runner ends. Scripts read the first two from their
# environment, and the runner ends shell tests' process groups itself.
#
# The library needs bash 3.2 or later and the POSIX utilities that ship with macOS and Linux. It
# writes the records to file descriptor 9, which it opens on the file that the runner names, so the
# script's own standard output and standard error stay free for the test's output.

# The declared settings' names and defaults, and the tests' names, as errata-run collects them.
_errata_setting_names=()
_errata_setting_defaults=()
_errata_test_names=()
# The settings that errata-run receives, as parallel arrays of names and values.
_errata_given_names=()
_errata_given_values=()
# The thread grant that errata-run receives, empty when it receives none.
_errata_threads=""
# `list` while errata-list writes the inventory, and `collect` while errata-run learns the names.
_errata_mode=""
# Whether errata-list has written a test record, after which no setting record may follow.
_errata_listed_test=""
# The file that errata_fail creates while a test runs, so that the harness learns of the failure.
_errata_failed_mark=""

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

# Prints its argument as a JSON string, quotes included.
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
  printf '"%s"' "$s"
}

# Prints a comma-separated list as a JSON array of strings.
_errata_json_list() {
  local items=() item out="" sep=""
  IFS=',' read -r -a items <<< "$1"
  for item in ${items[@]+"${items[@]}"}; do
    out+="$sep$(_errata_json_string "$item")"
    sep=","
  done
  printf '[%s]' "$out"
}

# Prints a comma-separated list of settings, each a name or `optional(name)`, as the JSON array of a
# test record's `settings` field.
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
    out+="$sep{\"name\":$(_errata_json_string "$name"),\"optional\":$optional}"
    sep=","
  done
  printf '[%s]' "$out"
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
      [ -z "$_errata_listed_test" ] ||
        _errata_misuse "the setting $name is declared after a test; declare settings in errata_settings"
      local record
      record="{\"type\":\"setting\",\"name\":$(_errata_json_string "$name")"
      record+=",\"description\":$(_errata_json_string "$description")"
      [ -n "$has_default" ] && record+=",\"default\":$(_errata_json_string "$default")"
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

# Declares a test: `errata_test NAME [--path a,b,c] [--file F] [--line N] [--description TEXT]
# [--tags a,b] [--settings a,optional(b)] [--threads N]`. Settings written `optional(b)` are ones
# the tests run without. The script calls it from `errata_tests`.
errata_test() {
  [ $# -ge 1 ] || _errata_misuse "errata_test takes a name"
  local name=$1
  shift
  local record
  record="{\"type\":\"test\",\"name\":$(_errata_json_string "$name")"
  while [ $# -gt 0 ]; do
    [ $# -ge 2 ] || _errata_misuse "$1 takes a value"
    case "$1" in
      --path | --tags | --settings)
        case "$2" in
          *$'\n'*) _errata_misuse "the value of $1 for the test $name holds a newline" ;;
        esac
        ;;
    esac
    case "$1" in
      --path) record+=",\"path\":$(_errata_json_list "$2")" ;;
      --file) record+=",\"file\":$(_errata_json_string "$2")" ;;
      --line)
        _errata_require_number --line "$2"
        record+=",\"line\":$2"
        ;;
      --description) record+=",\"description\":$(_errata_json_string "$2")" ;;
      --tags) record+=",\"tags\":$(_errata_json_list "$2")" ;;
      --settings) record+=",\"settings\":$(_errata_json_settings "$2")" ;;
      --threads)
        _errata_require_number --threads "$2"
        record+=",\"threads\":$2"
        ;;
      *) _errata_misuse "errata_test has no option $1" ;;
    esac
    shift 2
  done
  case "$_errata_mode" in
    list)
      errata_record "$record}"
      _errata_listed_test=1
      ;;
    collect) _errata_test_names+=("$name") ;;
  esac
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

# Prints the number of hardware threads that the runner granted the test, 1 when it granted none.
errata_threads() {
  printf '%s' "${_errata_threads:-1}"
}

# Fails the test: `errata_fail MESSAGE [DETAIL]` writes a verdict with the message and the detail,
# and returns 1.
errata_fail() {
  local record
  record="{\"type\":\"verdict\",\"status\":\"fail\",\"message\":$(_errata_json_string "$1")"
  [ $# -ge 2 ] && record+=",\"detail\":$(_errata_json_string "$2")"
  errata_record "$record}"
  if [ -n "$_errata_failed_mark" ]; then : > "$_errata_failed_mark"; fi
  return 1
}

# Prints the usage of a test executable.
_errata_usage() {
  cat >&2 <<EOF
usage:
  $0 errata-list <out>
  $0 errata-run <out> <test-name> [setting:NAME=VALUE]... [threads:N]

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

# Whether the script declares the test named by its argument.
_errata_known_test() {
  local t
  for t in ${_errata_test_names[@]+"${_errata_test_names[@]}"}; do
    [ "$t" = "$1" ] && return 0
  done
  return 1
}

# Performs one invocation, and returns its exit status.
_errata_invoke() {
  case "${1:-}" in
    errata-list)
      [ $# -eq 2 ] || { _errata_usage; return 2; }
      exec 9>>"$2"
      errata_record '{"type":"protocol","version":1}'
      _errata_mode=list
      _errata_listed_test=""
      if declare -F errata_settings > /dev/null; then errata_settings; fi
      if declare -F errata_tests > /dev/null; then errata_tests; fi
      _errata_mode=""
      exec 9>&-
      return 0
      ;;
    errata-run)
      [ $# -ge 3 ] || { _errata_usage; return 2; }
      local out=$2 name=$3 arg setting status
      shift 3
      _errata_given_names=()
      _errata_given_values=()
      _errata_threads=""
      for arg in "$@"; do
        case "$arg" in
          setting:*)
            setting=${arg#setting:}
            _errata_given_names+=("${setting%%=*}")
            case "$setting" in
              *=*) _errata_given_values+=("${setting#*=}") ;;
              *) _errata_given_values+=("") ;;
            esac
            ;;
          threads:*) _errata_threads=${arg#threads:} ;;
        esac
      done
      exec 9>>"$out"
      errata_record '{"type":"protocol","version":1}'
      _errata_setting_names=()
      _errata_setting_defaults=()
      _errata_test_names=()
      _errata_mode=collect
      if declare -F errata_settings > /dev/null; then errata_settings; fi
      if declare -F errata_tests > /dev/null; then errata_tests; fi
      _errata_mode=""
      if ! _errata_known_test "$name"; then
        printf 'no test is named %s\n' "$name" >&2
        errata_record "{\"type\":\"verdict\",\"status\":\"error\",\"message\":$(_errata_json_string "no test is named $name")}"
        exec 9>&-
        return 1
      fi
      declare -F errata_run_test > /dev/null ||
        _errata_misuse "the script declares tests and defines no errata_run_test"
      errata_record "{\"type\":\"start\",\"time_ms\":$(_errata_now_ms)}"
      local errexit="" marks
      marks=$(mktemp -d)
      _errata_failed_mark="$marks/failed"
      case $- in *e*) errexit=1 ;; esac
      # The test runs in a subshell, so that its `exit` ends only the test, and with `errexit`, so
      # that a failing command ends it. Bash honors `errexit` only in a subshell that is a command
      # of its own, outside any condition.
      set +e
      (set -e; errata_run_test "$name")
      status=$?
      [ -n "$errexit" ] && set -e
      # Tests that failed with `errata_fail` exit with 1, whatever their bodies returned.
      [ -e "$_errata_failed_mark" ] && status=1
      rm -rf "$marks"
      _errata_failed_mark=""
      exec 9>&-
      return "$status"
      ;;
    errata-fixture)
      printf 'errata.sh: the shell harness runs the modes errata-list and errata-run\n' >&2
      return 2
      ;;
    *)
      _errata_usage
      return 2
      ;;
  esac
}

# The main of a test executable. It performs the invocation that its arguments give, or each
# invocation of a chain whose invocations are separated by a ';' argument, in order, stopping at the
# first that exits non-zero, and exits with the status of the last that ran. `errata-list` writes the
# inventory: the settings that `errata_settings` declares, then the tests that `errata_tests`
# declares. `errata-run` runs one test with `errata_run_test NAME` in a subshell with `set -e`, so
# that a command that fails ends the test, and exits with its status, or with 1 when the test called
# `errata_fail`.
errata_main() {
  local status=2 invocation
  [ $# -gt 0 ] || { _errata_usage; exit 2; }
  while [ $# -gt 0 ]; do
    invocation=()
    while [ $# -gt 0 ] && [ "$1" != ";" ]; do
      invocation+=("$1")
      shift
    done
    [ $# -gt 0 ] && shift
    # The invocation is a command of its own, outside any condition, so that the test's `errexit`
    # takes effect.
    set +e
    _errata_invoke ${invocation[@]+"${invocation[@]}"}
    status=$?
    [ "$status" -eq 0 ] || break
  done
  exit "$status"
}
