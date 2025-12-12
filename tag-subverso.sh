#!/bin/bash

# While SubVerso works in every Lean release, a Verso project and the
# code that it's documenting must have the same version of SubVerso.
# Most projects should rely on a tagged version of Verso that
# corresponds to a Lean release, but this doesn't provide an easy way
# to keep the versions of SubVerso synchronized. This can be solved by
# tagging SubVerso for each Verso tag.

# This script iterates over Verso's Lean release tags and creates a
# tag in SubVerso for each of them. It is idempotent and can be run
# for each Lean release.

set -euo pipefail

# Check dependencies
for cmd in git jq; do
    if ! command -v "$cmd" &> /dev/null; then
        echo "Error: Required command '$cmd' not found" >&2
        exit 1
    fi
done

# Configuration
ORG="leanprover"
VERSO_REPO="verso"
SUBVERSO_REPO="subverso"
WORK_DIR=$(mktemp -d)
DRY_RUN=false
PUSH_TAGS=false

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --dry-run)
            DRY_RUN=true
            shift
            ;;
        --push)
            PUSH_TAGS=true
            shift
            ;;
        -h|--help)
            echo "Usage: $0 [--dry-run] [--push]"
            echo "  --dry-run    Show what tags would be created without actually creating them"
            echo "  --push       Push created tags to remote (by default tags are only created locally)"
            exit 0
            ;;
        *)
            echo "Unknown option: $1" >&2
            exit 1
            ;;
    esac
done

# Cleanup function
cleanup() {
    rm -rf "$WORK_DIR"
}
trap cleanup EXIT

# Determine git URL format based on available authentication
get_git_url() {
    local repo=$1
    if [[ -n "${GITHUB_TOKEN:-}" ]]; then
        echo "https://${GITHUB_TOKEN}@github.com/${ORG}/${repo}.git"
    else
        echo "git@github.com:${ORG}/${repo}.git"
    fi
}

echo "Working directory: $WORK_DIR"
cd "$WORK_DIR"

# Safety check: ensure the work directory is empty
if [[ -n "$(ls -A)" ]]; then
    echo "Error: Work directory is not empty: $PWD" >&2
    exit 1
fi

# Clone repositories
echo "Cloning repositories..."
if ! git clone --quiet "$(get_git_url "$VERSO_REPO")" verso-repo; then
    echo "Error: Failed to clone $VERSO_REPO. Check authentication." >&2
    exit 1
fi
if ! git clone --quiet "$(get_git_url "$SUBVERSO_REPO")" subverso-repo; then
    echo "Error: Failed to clone $SUBVERSO_REPO. Check authentication." >&2
    exit 1
fi

cd verso-repo

# Get all v4* tags from Verso repo
echo "Finding v4* tags in $VERSO_REPO..."
verso_tags=$(git tag -l 'v4*' | sort -t. -k1,1n -k2,2n -k3,3n 2>/dev/null || git tag -l 'v4*' | sort)
if [[ -z "$verso_tags" ]]; then
    echo "No v4* tags found in $VERSO_REPO"
    exit 0
fi

tag_count=$(echo "$verso_tags" | wc -l | tr -d ' ')
echo "Found $tag_count v4* tags"

cd ../subverso-repo

# Get existing verso-* tags from SubVerso repo
git fetch --tags origin
existing_subverso_tags=$(git tag -l 'verso-*' | sed 's/^verso-//' | sort -t. -k1,1n -k2,2n -k3,3n 2>/dev/null || git tag -l 'verso-*' | sed 's/^verso-//' | sort)

cd ../verso-repo

# Process each Verso tag
tags_to_create=()
while IFS= read -r tag; do
    subverso_tag="verso-$tag"

    # Check if SubVerso tag already exists
    if echo "$existing_subverso_tags" | grep -qx "$tag"; then
        echo "Tag $subverso_tag already exists, skipping"
        continue
    fi

    # Checkout the tag
    git checkout --quiet "$tag"

    # Check if lake-manifest.json exists
    if [[ ! -f "lake-manifest.json" ]]; then
        echo "Warning: lake-manifest.json not found for tag $tag, skipping"
        continue
    fi

    # Extract SubVerso hash
    subverso_hash=$(jq -r '.packages[] | select(.name == "subverso") | .rev' lake-manifest.json)

    if [[ -z "$subverso_hash" || "$subverso_hash" == "null" ]]; then
        echo "Warning: Could not find subverso hash for tag $tag, skipping"
        continue
    fi

    # Verify the hash exists in the SubVerso repo
    cd ../subverso-repo
    if ! git cat-file -e "$subverso_hash" 2>/dev/null; then
        echo "Warning: Hash $subverso_hash not found in $SUBVERSO_REPO for tag $tag, skipping"
        cd ../verso-repo
        continue
    fi

    tags_to_create+=("$tag:$subverso_hash")
    echo "Will create tag $subverso_tag at $subverso_hash"

    cd ../verso-repo
done <<< "$verso_tags"

# Create the tags
if [[ ${#tags_to_create[@]} -eq 0 ]]; then
    echo "No tags to create"
    exit 0
fi

echo ""
echo "Summary: ${#tags_to_create[@]} tags to create"

if [[ "$DRY_RUN" == "true" ]]; then
    echo "DRY RUN - would create the following tags:"
    for entry in "${tags_to_create[@]}"; do
        tag=${entry%:*}
        hash=${entry#*:}
        echo "  verso-$tag -> $hash"
    done
    exit 0
fi

cd ../subverso-repo

echo "Creating tags..."
for entry in "${tags_to_create[@]}"; do
    tag=${entry%:*}
    hash=${entry#*:}
    subverso_tag="verso-$tag"

    echo "Creating tag $subverso_tag at $hash"
    git tag "$subverso_tag" "$hash"
done

# Push all new tags
if [[ "$PUSH_TAGS" == "true" ]]; then
    echo "Pushing tags to remote..."
    for entry in "${tags_to_create[@]}"; do
        tag=${entry%:*}
        subverso_tag="verso-$tag"
        echo "Pushing tag $subverso_tag"
        git push origin "$subverso_tag"
    done
    echo "Done! Created and pushed ${#tags_to_create[@]} tags"
else
    echo "Done! Created ${#tags_to_create[@]} tags locally (use --push to push to remote)"
fi
