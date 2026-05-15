#!/usr/bin/env python3
import argparse
import os
from release_utils import (
    run_git_command,
    is_git_ancestor,
    find_latest_version,
    find_latest_stable_version,
)
from pathlib import Path

UNICODE_INPUT_FILES = [
    "unicode-input.min.js",
    "unicode-input-component.min.js",
]

STATS_HTML_FILE = "stats.html"


def add_metadata(directory, version_name, extensions=(".html", ".htm")):
    """
    Recursively walk through `directory`, find all HTML files,
    and insert noindex and canonical URL tags into <head>.

    Args:
      directory (Path): The directory in which to recursively modify files
      version_name (str): The version name (e.g. "4.25.0-rc2", "latest", "stable")
    """
    for root, _, files in os.walk(directory):
        for filename in files:
            if filename.lower().endswith(extensions):
                filepath = os.path.join(root, filename)
                with open(filepath, "r", encoding="utf-8", errors="ignore") as f:
                    content = f.read()

                # Only edit if <head> exists and we haven't already added the meta tag
                if "<head>" in content and 'name="robots"' not in content:
                    # Canonical URL always points to the latest/ version
                    relative = os.path.relpath(root, directory)
                    if relative == ".":
                        canonical_path = f"latest/{filename}"
                    else:
                        canonical_path = f"latest/{relative}/{filename}"
                    href = f"https://verso.lean-lang.org/doc/{canonical_path}".removesuffix(
                        "index.html"
                    )

                    noindex = (
                        ""
                        if version_name == "latest"
                        else '\n<meta name="robots" content="noindex">'
                    )
                    new_content = content.replace(
                        "<head>",
                        f'<head>{noindex}\n<link rel="canonical" href="{href}" />\n',
                    )

                    # Write back the modified file
                    with open(filepath, "w", encoding="utf-8") as f:
                        f.write(new_content)
                    print(f"Updated: {filepath}")
                else:
                    print(f"Skipped: {filepath}")


def replace_unicode_input_files(directory, unicode_input_files):
    """
    Recursively walk through `directory`, find all -verso-search subdirectories,
    and replace Unicode input JS files with the provided contents from main.

    Args:
        directory (Path): The version directory to search within
        unicode_input_files (dict): Map from filename to bytes content
    """
    for root, dirs, files in os.walk(directory):
        if os.path.basename(root) == "-verso-search":
            for filename, content in unicode_input_files.items():
                filepath = os.path.join(root, filename)
                if os.path.exists(filepath):
                    with open(filepath, "wb") as f:
                        f.write(content)
                    print(f"Replaced Unicode input file: {filepath}")
                else:
                    print(f"Skipped (not present): {filepath}")


def inject_stats_html(directory, stats_html_content, extensions=(".html", ".htm")):
    """
    Recursively walk through `directory`, find all HTML files,
    and insert stats_html_content as the last element of <head>.

    Args:
        directory (Path): The directory in which to recursively modify files
        stats_html_content (str): HTML content to inject before </head>
    """
    for root, _, files in os.walk(directory):
        for filename in files:
            if filename.lower().endswith(extensions):
                filepath = os.path.join(root, filename)
                with open(filepath, "r", encoding="utf-8", errors="ignore") as f:
                    content = f.read()

                if "</head>" in content:
                    new_content = content.replace(
                        "</head>", f"{stats_html_content}</head>"
                    )
                    with open(filepath, "w", encoding="utf-8") as f:
                        f.write(new_content)
                    print(f"Injected stats HTML: {filepath}")
                else:
                    print(f"Skipped stats HTML injection (no </head>): {filepath}")


# This function is the right thing to change to change the
# content of the overlays that are applied.
def apply_overlays(deploy_dir, unicode_input_files=None, stats_html_content=None):
    """
    Apply desired overlays inside current directory.

    Args:
        deploy_dir (str): Directory containing all versions
        unicode_input_files (dict): Map from filename to bytes content, read
            from main before switching to the deploy branch. If None or empty,
            the Unicode input file replacement overlay is skipped.
        stats_html_content (str): Content of stats.html from main. If None,
            the stats HTML injection overlay is skipped.
    """
    latest_version = find_latest_version(deploy_dir)
    latest_stable_version = find_latest_stable_version(deploy_dir)
    print(f"overlay.py: the latest version is {latest_version}")
    print(f"overlay.py: the latest stable version is {latest_stable_version}")
    for inner in Path(deploy_dir).iterdir():
        # Check for index.html to identify version directories
        if inner.is_dir() and (inner / "index.html").is_file():
            add_metadata(inner, str(inner))
            if unicode_input_files:
                replace_unicode_input_files(inner, unicode_input_files)
            if stats_html_content is not None:
                inject_stats_html(inner, stats_html_content)


def deploy_overlays(deploy_dir, src_branch, tgt_branch):
    """
    Apply desired overlays inside deploy_dir.

    Args:
        deploy_dir (str): Directory that contains all versions of the site.
            This is the content we expect to find at branch `src_branch`, and
            this function modifies it in place to produce a repository state
            suitable for committing to branch `tgt_branch`.
        src_branch (str): Git branch to apply overlays to
        tgt_branch (str): Git branch to commit to
    """
    os.chdir(deploy_dir)
    # Save current git commit to restore later
    current_branch = run_git_command(["git", "branch", "--show-current"])

    # Read Unicode input files from the current branch (main) before switching
    unicode_input_files = {}
    for filename in UNICODE_INPUT_FILES:
        filepath = Path(deploy_dir) / "static-web" / "search" / filename
        if filepath.exists():
            with open(filepath, "rb") as f:
                unicode_input_files[filename] = f.read()
            print(f"overlay.py: read Unicode input file from main: {filepath}")
        else:
            print(
                f"overlay.py: Unicode input file not found on main, skipping: {filepath}"
            )

    # Read stats.html from the current branch (main) before switching
    stats_html_content = None
    stats_html_path = Path(deploy_dir) / "doc" / STATS_HTML_FILE
    if stats_html_path.exists():
        with open(stats_html_path, "r", encoding="utf-8") as f:
            stats_html_content = f.read()
        print(f"overlay.py: read stats HTML from main: {stats_html_path}")
    else:
        print(f"overlay.py: stats HTML not found on main, skipping: {stats_html_path}")

    try:
        if is_git_ancestor(tgt_branch, src_branch):
            raise Exception(
                f"Git merge will have bad behavior if {tgt_branch} is an ancestor of "
                f"{src_branch}. Try creating a vacuous commit on {tgt_branch} first."
            )
        run_git_command(["git", "switch", src_branch])

        if find_latest_version(deploy_dir) is None:
            print(f"No version directories found on {src_branch}, nothing to overlay")
            return

        print("Applying overlays...")
        apply_overlays(deploy_dir, unicode_input_files, stats_html_content)
        print("Creating merge commit...")
        # Add version directories and aliases (stable may not exist for RC releases)
        add_paths = ["4*", "latest"]
        if Path("stable").exists():
            add_paths.append("stable")
        run_git_command(["git", "add"] + add_paths)
        # We create the overlay commit based on src_branch...
        run_git_command(["git", "commit", "-m", "overlay.py: apply overlays"])
        # ...but we actually want to add it to the history of
        # tgt_branch. This is the moment when it is problematic
        # for tgt_branch to be an ancestor of src_branch, because then this
        # will be a no-op, despite --no-ff.
        #
        # All of this complication is due to the fact that "-s theirs" doesn't
        # exist and "-X theirs" isn't what we want.
        # (see https://stackoverflow.com/questions/4911794 for context)
        run_git_command(
            [
                "git",
                "merge",
                "-m",
                "merge overlays",
                "--no-ff",
                "--no-edit",
                "-s",
                "ours",
                tgt_branch,
            ]
        )
        run_git_command(["git", "switch", tgt_branch])
        run_git_command(["git", "reset", "--hard", src_branch, "--"])
        run_git_command(["git", "switch", src_branch])
        # Rewind the src_branch back past the merge commit and the
        # overlay commit. This cleanup probably isn't strictly necessary
        # in prod, since we don't expect our GH Actions caller script to
        # push the src_branch, but it's helpful for testing.
        run_git_command(["git", "reset", "--hard", "HEAD^^"])
    finally:
        run_git_command(["git", "switch", current_branch])


def main():
    parser = argparse.ArgumentParser(
        description="Apply overlays to a deployment branch"
    )
    parser.add_argument("deploy_dir", help="Directory to operate on")
    parser.add_argument("src_branch", help="Git branch to apply overlays to")
    parser.add_argument("tgt_branch", help="Git branch to commit to")

    args = parser.parse_args()

    print(
        f"Applying overlays to {args.deploy_dir} branch {args.src_branch} to produce {args.tgt_branch}"
    )

    deploy_overlays(args.deploy_dir, args.src_branch, args.tgt_branch)


if __name__ == "__main__":
    main()
