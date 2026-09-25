#!/usr/bin/env bash
# A test executable for a browser suite whose site a Lake workspace of its own builds. When a test
# runs, the script builds the site, then hands the invocation to Verso's pytest harness with
# `--site-dir` naming the site; a listing needs no site and starts the harness at once. The site is
# built once per run: a stamp named after the runner's ERRATA_RUN_ID records the site, and without
# the variable every invocation builds it. A lock directory per test project makes the check and
# the build one step, so two suites of one test project never build at once.
#
#   errata_with_site.sh literate PROJECT PYTEST-ARG... MODE ARG...
#     the literate HTML of the test project PROJECT, which `lake query :literateHtml` builds there
#   errata_with_site.sh verso-html PROJECT TARGET PYTEST-ARG... MODE ARG...
#     the site that `verso-html` writes from the literate JSON of PROJECT, which `lake build TARGET`
#     builds there
#
# MODE is `errata-list` or `errata-run`, as the Errata runner passes it, and the script runs from
# the repository's root.

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
  # The stamps of this site are named after the runs that built it. Outside a run, which gives no
  # ERRATA_RUN_ID, every invocation builds the site.
  prefix="$stamp_dir/$kind-$(basename "$project")"
  run_id="${ERRATA_RUN_ID:-}"
  stamp="$prefix.$run_id.stamp"
  take_lock
  trap release_lock EXIT
  site=""
  if [ -n "$run_id" ] && [ -f "$stamp" ]; then
    site=$(cat "$stamp")
  fi
  if [ -z "$site" ] || [ ! -d "$site" ]; then
    echo "Building the site of $project..."
    site=$(build_site)
    rm -f "$prefix".*.stamp
    if [ -n "$run_id" ]; then
      printf '%s\n' "$site" > "$stamp.$$"
      mv "$stamp.$$" "$stamp"
    fi
  fi
  release_lock
  trap - EXIT
else
  site="$PWD/$project/.lake/build/literate-html"
fi

exec uv run --project browser-tests --extra test python browser-tests/errata_pytest.py \
  ${pytest_args[@]+"${pytest_args[@]}"} --site-dir "$site" "$@"
