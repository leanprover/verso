#!/usr/bin/env bash
# A test executable for a browser suite whose site a Lake workspace of its own builds. When a test
# runs, the script builds the site, then hands the invocation to Verso's pytest harness with
# `--site-dir` naming the site; a listing needs no site and starts the harness at once. The site is
# built once for each process that starts the tests, which is the runner in a run: a stamp records
# that process's identifier and start time. A lock directory per test project makes the check and
# the build one step, so two suites of one test project never build at once. This script stands in
# for a fixture that builds the site.
#
#   errata_with_site.sh literate PROJECT PYTEST-ARG... MODE ARG...
#     the literate HTML of the test project PROJECT, which `lake query :literateHtml` builds there
#   errata_with_site.sh verso-html PROJECT TARGET PYTEST-ARG... MODE ARG...
#     the site that `verso-html` writes from the literate JSON of PROJECT, which `lake build TARGET`
#     builds there
#
# MODE is `errata-list` or `errata-run`, as the Errata runner passes it, and the script runs from the
# repository's root.

set -euo pipefail

kind=$1
project=$2
shift 2
case "$kind" in
  literate) ;;
  verso-html)
    target=$1
    shift
    ;;
  *)
    echo "errata_with_site.sh: unknown kind of site '$kind'" >&2
    exit 2
    ;;
esac

# The pytest arguments are everything before the protocol's mode.
pytest_args=()
while [ $# -gt 0 ]; do
  case "$1" in
    errata-list | errata-run | errata-fixture) break ;;
  esac
  pytest_args+=("$1")
  shift
done

# Builds the site, and prints its directory.
build_site() {
  case "$kind" in
    literate)
      (cd "$project" && lake query :literateHtml)
      ;;
    verso-html)
      local out="$PWD/.lake/build/sites/verso-html"
      (cd "$project" && lake build "$target") >&2
      rm -rf "$out"
      lake exe verso-html "$project/.lake/build/literate" "$out" >&2
      printf '%s\n' "$out"
      ;;
  esac
}

stamp_dir="$PWD/.lake/build/sites"
lock="$stamp_dir/$(basename "$project").lock"

# Takes the lock of the test project, which one build at a time holds. A lock whose holder has
# exited is taken over.
take_lock() {
  mkdir -p "$stamp_dir"
  until mkdir "$lock" 2>/dev/null; do
    local holder
    holder=$(cat "$lock/pid" 2>/dev/null || true)
    if [ -n "$holder" ] && ! kill -0 "$holder" 2>/dev/null; then
      rm -rf "$lock"
    else
      sleep 0.2
    fi
  done
  echo $$ > "$lock/pid"
}

# Releases the lock of the test project.
release_lock() {
  rm -rf "$lock"
}

if [ "${1:-}" = errata-run ]; then
  stamp="$stamp_dir/$kind-$(basename "$project").stamp"
  # The process that starts the tests, the runner in a run, identified by its process identifier
  # and its start time. Without a start time, every invocation builds the site.
  started=$(ps -o lstart= -p "$PPID" 2>/dev/null || true)
  starter=""
  [ -n "$started" ] && starter="$PPID $started"
  take_lock
  trap release_lock EXIT
  site=""
  if [ -n "$starter" ] && [ -f "$stamp" ] && [ "$(sed -n 1p "$stamp")" = "$starter" ]; then
    site=$(sed -n 2p "$stamp")
  fi
  if [ -z "$site" ] || [ ! -d "$site" ]; then
    echo "Building the site of $project..."
    site=$(build_site)
    if [ -n "$starter" ]; then
      printf '%s\n%s\n' "$starter" "$site" > "$stamp.$$"
      mv "$stamp.$$" "$stamp"
    else
      rm -f "$stamp"
    fi
  fi
  release_lock
  trap - EXIT
else
  site="$PWD/$project/.lake/build/literate-html"
fi

exec uv run --project browser-tests --extra test python browser-tests/errata_pytest.py \
  ${pytest_args[@]+"${pytest_args[@]}"} --site-dir "$site" "$@"
