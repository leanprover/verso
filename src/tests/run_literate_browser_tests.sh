#!/usr/bin/env bash
set -euo pipefail

# Run Playwright browser tests against the literate test projects.
#
#   run_literate_browser_tests.sh               build every site, then test each one
#   run_literate_browser_tests.sh build         build every site
#   run_literate_browser_tests.sh test PROJECT [PYTEST_ARG...]
#                                               test the site that was built for PROJECT,
#                                               passing the remaining arguments to pytest
#
# Each test project is built via `lake query :literateHtml` (which builds and
# prints the output path). The site is then copied to `_out/literate-sites`,
# and pytest is pointed at the copy, so the tests read a site that stays the
# same while Lake runs in the test project again.

PROJECTS=(literate-config literate-multi-root)
SITES_DIR="_out/literate-sites"

# Sets `test_dir` and `label` for a project.
describe() {
    case "$1" in
        literate-config)
            test_dir="browser-tests/literate"
            label="Literate"
            ;;
        literate-multi-root)
            test_dir="browser-tests/literate-multi-root"
            label="Multi-root literate"
            ;;
        *)
            echo "Unknown literate test project: $1" >&2
            echo "Known projects: ${PROJECTS[*]}" >&2
            exit 1
            ;;
    esac
}

build_site() {
    local project="$1"
    local site_dir

    describe "$project"
    echo "Building literate HTML for test-projects/${project}..."
    site_dir=$(cd "test-projects/${project}" && lake query :literateHtml)

    mkdir -p "$SITES_DIR"
    rm -rf "${SITES_DIR:?}/${project}"
    cp -R "$site_dir" "${SITES_DIR}/${project}"
    echo "  ${label} site is at ${SITES_DIR}/${project}"
}

test_site() {
    local project="$1"
    local site_dir="${SITES_DIR}/${project}"
    shift

    describe "$project"
    if [[ ! -d "$site_dir" ]]; then
        echo "${site_dir} doesn't exist; run '$0 build' first" >&2
        exit 1
    fi

    echo "Running ${label} browser tests against ${site_dir}..."
    uv run --project browser-tests --extra test \
        pytest "$test_dir" -v --site-dir "$(pwd)/${site_dir}" "$@"
    echo "  ${label} browser tests passed!"
}

build_sites() {
    for project in "${PROJECTS[@]}"; do build_site "$project"; done
}

case "${1:-all}" in
    all)
        build_sites
        for project in "${PROJECTS[@]}"; do test_site "$project"; done
        ;;
    build)
        build_sites
        ;;
    test)
        if [[ $# -lt 2 ]]; then
            echo "usage: $0 test PROJECT [PYTEST_ARG...]" >&2
            exit 1
        fi
        shift
        test_site "$@"
        ;;
    *)
        echo "usage: $0 [build | test PROJECT [PYTEST_ARG...]]" >&2
        exit 1
        ;;
esac
