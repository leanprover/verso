#!/usr/bin/env bash
set -euo pipefail

# Run Playwright browser tests against the literate test projects.
# Each test project is built via `lake query :literateHtml` (which
# builds and prints the output path), then pytest is pointed at the result.

run_tests() {
    local project_dir="$1"
    local test_dir="$2"
    local label="$3"

    echo "Running ${label} browser tests..."
    echo "  Building literate HTML for ${project_dir}..."

    site_dir=$(cd "$project_dir" && lake query :literateHtml)

    echo "  Running Playwright tests against ${site_dir}..."
    uv run --project browser-tests --extra test \
        pytest "$test_dir" -v --site-dir "$site_dir"

    echo "  ${label} browser tests passed!"
}

run_tests "test-projects/literate-config" \
    "browser-tests/literate" \
    "Literate"

run_tests "test-projects/literate-multi-root" \
    "browser-tests/literate-multi-root" \
    "Multi-root literate"
