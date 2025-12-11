#!/usr/bin/env bash

# Script to check that all text files have trailing newlines
# Configuration is read from .github/trailing-newlines-config.txt

set -euo pipefail

CONFIG_FILE=".github/trailing-newlines-config.txt"

if [ ! -f "$CONFIG_FILE" ]; then
    echo "Error: Configuration file $CONFIG_FILE not found"
    exit 1
fi

# Read configuration
EXTENSIONS=()
SKIP_LIST=()
READING_SECTION=""

while IFS= read -r line || [ -n "$line" ]; do
    # Skip empty lines and comments
    [[ -z "$line" || "$line" =~ ^[[:space:]]*# ]] && continue

    # Check for section headers
    if [[ "$line" == "[extensions]" ]]; then
        READING_SECTION="extensions"
        continue
    elif [[ "$line" == "[skip]" ]]; then
        READING_SECTION="skip"
        continue
    fi

    # Add to appropriate array
    if [[ "$READING_SECTION" == "extensions" ]]; then
        EXTENSIONS+=("$line")
    elif [[ "$READING_SECTION" == "skip" ]]; then
        SKIP_LIST+=("$line")
    fi
done < "$CONFIG_FILE"

echo "Checking files with extensions: ${EXTENSIONS[*]}"
if [ ${#SKIP_LIST[@]} -gt 0 ]; then
    echo "Skipped patterns: ${SKIP_LIST[*]}"
fi

# Get all tracked files from git
FILES_MISSING_NEWLINE=()

while IFS= read -r file; do
    # Check if file matches any of the extensions
    MATCHES=false
    for ext in "${EXTENSIONS[@]}"; do
        if [[ "$file" == *"$ext" ]]; then
            MATCHES=true
            break
        fi
    done

    if [ "$MATCHES" = false ]; then
        continue
    fi

    # Check if file matches skip patterns (using glob matching)
    SHOULD_SKIP=false
    for skip_pattern in "${SKIP_LIST[@]}"; do
        # shellcheck disable=SC2053
        if [[ "$file" == $skip_pattern ]]; then
            SHOULD_SKIP=true
            break
        fi
    done

    if [ "$SHOULD_SKIP" = true ]; then
        echo "Skipping file: $file"
        continue
    fi

    # Check if file exists and is not empty
    if [ ! -f "$file" ] || [ ! -s "$file" ]; then
        continue
    fi

    # Check if file ends with a newline
    # Read the last byte of the file
    if [ -n "$(tail -c 1 "$file")" ]; then
        FILES_MISSING_NEWLINE+=("$file")
    fi
done < <(git ls-files)

# Report results
if [ ${#FILES_MISSING_NEWLINE[@]} -eq 0 ]; then
    echo "✓ All text files have trailing newlines"
    exit 0
else
    echo "✗ The following files are missing trailing newlines:"
    printf '%s\n' "${FILES_MISSING_NEWLINE[@]}"
    exit 1
fi
