#!/bin/bash

RUN_DIR=src/tests/interactive

# Configuration
TEST_DIR="$RUN_DIR/test-cases"
RUNNER="$RUN_DIR/test_single.sh"
PASS_COUNT=0
FAIL_COUNT=0
FAILED_TESTS=()

# Check if the runner exists and is executable
if [[ ! -x "$RUNNER" ]]; then
    echo "Error: Runner script '$RUNNER' not found or not executable."
    exit 1
fi

echo "------------------------------------------------"
echo " Starting Verso Interactive Test Suite: $(date) "
echo "------------------------------------------------"

# Loop through every file in the test directory
for test_file in "$TEST_DIR"/*.lean; do
    # Skip if it's not a file (e.g., a subdirectory)
    [[ -f "$test_file" ]] || continue

    echo -n "Running test: $(basename "$test_file")... "

    # Capture both stdout and stderr into a variable
    # This allows us to hide it on PASS and show it on FAIL
    TEST_OUTPUT=$("$RUNNER" "$test_file" 2>&1)
    EXIT_CODE=$?

    if [ $EXIT_CODE -eq 0 ]; then
        echo "✅ PASS"
        ((PASS_COUNT++))
    else
        echo "❌ FAIL (Exit Code: $EXIT_CODE)"
        echo "--- FAILURE LOG: $(basename "$test_file") ---"
        echo "$TEST_OUTPUT"
        echo "-----------------------------------------------"

        ((FAIL_COUNT++))
        FAILED_TESTS+=("$(basename "$test_file")")
    fi
done

# --- Summary Output ---
echo "-----------------------------------------------"
echo "Test Summary:"
echo "  Total:  $((PASS_COUNT + FAIL_COUNT))"
echo "  Passed: $PASS_COUNT"
echo "  Failed: $FAIL_COUNT"

if [[ $FAIL_COUNT -gt 0 ]]; then
    echo "-----------------------------------------------"
    echo "Failed Tests:"
    for failed in "${FAILED_TESTS[@]}"; do
        echo "  - $failed"
    done
    echo "-----------------------------------------------"
    exit 1
else
    echo "All tests passed successfully!"
    echo "-----------------------------------------------"
    exit 0
fi
