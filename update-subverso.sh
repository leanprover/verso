#!/bin/bash
set -euo pipefail

# Extract subverso information from root manifest
ROOT_MANIFEST="./lake-manifest.json"

# Extract required fields for validation
SUBVERSO_REV=$(jq -r '.packages[] | select(.name == "subverso") | .rev' "$ROOT_MANIFEST")
SUBVERSO_URL=$(jq -r '.packages[] | select(.name == "subverso") | .url' "$ROOT_MANIFEST")

# Ensure we found subverso in the root manifest
if [ -z "$SUBVERSO_REV" ]; then
    echo "Error: Could not find 'subverso' package in root manifest"
    exit 1
fi

echo "Found subverso rev: $SUBVERSO_REV"
echo "Found subverso url: $SUBVERSO_URL"

# Find all lake-manifest.json files in the repo (excluding the root one)
find . -name "lake-manifest.json" -not -path "$ROOT_MANIFEST" | grep -v "\.lake" | while read -r manifest_file; do
    echo "Processing $manifest_file..."

    # Check if the manifest contains subverso package
    if jq -e '.packages[] | select(.name == "subverso")' "$manifest_file" > /dev/null; then

        # Get actual values for comparison
        ACTUAL_URL=$(jq -r '.packages[] | select(.name == "subverso") | .url' "$manifest_file")
        ACTUAL_TYPE=$(jq -r '.packages[] | select(.name == "subverso") | .type' "$manifest_file")
        ACTUAL_INPUT_REV=$(jq -r '.packages[] | select(.name == "subverso") | .inputRev' "$manifest_file")

        # Validate URL
        if [ "$ACTUAL_URL" != "$SUBVERSO_URL" ]; then
            echo "Error in $manifest_file: URL mismatch"
            echo "  Expected: $SUBVERSO_URL"
            echo "  Actual:   $ACTUAL_URL"
            exit 1
        fi

        # Validate type
        if [ "$ACTUAL_TYPE" != "git" ]; then
            echo "Error in $manifest_file: Type mismatch"
            echo "  Expected: git"
            echo "  Actual:   $ACTUAL_TYPE"
            exit 1
        fi

        # Validate inputRev
        if [ "$ACTUAL_INPUT_REV" != "main" ]; then
            echo "Error in $manifest_file: InputRev mismatch"
            echo "  Expected: main"
            echo "  Actual:   $ACTUAL_INPUT_REV"
            exit 1
        fi

        # Update the rev field for subverso
        jq --arg rev "$SUBVERSO_REV" '.packages = (.packages | map(
            if .name == "subverso" then
                .rev = $rev
            else
                .
            end
        ))' "$manifest_file" > "${manifest_file}.tmp"

        # Replace the original file
        mv "${manifest_file}.tmp" "$manifest_file"
        echo "Updated $manifest_file"
    else
        echo "No subverso package found in $manifest_file, skipping"
    fi
done

echo "All manifests processed successfully"
