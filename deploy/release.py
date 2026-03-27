#!/usr/bin/env python3
import os
import sys
import shutil
import tempfile
import argparse
import datetime
import functools
from release_utils import (
    run_git_command, find_latest_version, find_latest_stable_version,
    git_has_changes, parse_version, compare_versions
)


def stamp_html_files(source_dir, commit_sha):
    """Prepend a commit stamp comment to every HTML file in source_dir."""
    timestamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    stamp = f"<!-- Generated from commit {commit_sha} at {timestamp} -->\n"
    for root, _, files in os.walk(source_dir):
        for filename in files:
            if filename.lower().endswith((".html", ".htm")):
                filepath = os.path.join(root, filename)
                with open(filepath, "r", encoding="utf-8") as f:
                    content = f.read()
                with open(filepath, "w", encoding="utf-8") as f:
                    f.write(stamp + content)


def generate_index_html(latest_version, stable_version):
    """Generate a root index.html listing all available versions."""
    # Collect version directories
    version_dirs = []
    for d in os.listdir("."):
        if os.path.isdir(d) and d not in ("latest", "stable"):
            pv = parse_version(d)
            if pv is not None and pv["type"] is not None:
                version_dirs.append((d, pv))

    # Sort newest first
    def version_cmp(a, b):
        result = compare_versions(a[1], b[1])
        if result is None:
            return 0
        return -result

    version_dirs.sort(key=functools.cmp_to_key(version_cmp))

    # Build version list HTML
    items = []
    for name, _ in version_dirs:
        badges = ""
        if name == latest_version:
            badges += ' <span class="badge latest">latest</span>'
        if name == stable_version:
            badges += ' <span class="badge stable">stable</span>'
        items.append(f'<li><a href="{name}/">{name}</a>{badges}</li>')
    version_list = "\n".join(items)

    stable_link = ""
    if stable_version:
        stable_link = f'<a href="stable/">Latest stable ({stable_version})</a> &middot; '

    latest_link = ""
    if latest_version:
        latest_link = f'<a href="latest/">Latest version ({latest_version})</a>'

    html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Verso User's Guide — All Versions</title>
<style>
body {{ font-family: system-ui, -apple-system, sans-serif; max-width: 600px; margin: 2rem auto; padding: 0 1rem; color: #333; }}
h1 {{ font-size: 1.5rem; }}
ul {{ list-style: none; padding: 0; }}
li {{ padding: 0.4rem 0; }}
a {{ color: #2563eb; text-decoration: none; }}
a:hover {{ text-decoration: underline; }}
.badge {{ font-size: 0.75rem; padding: 0.1rem 0.4rem; border-radius: 0.25rem; margin-left: 0.5rem; }}
.latest {{ background: #dbeafe; color: #1e40af; }}
.stable {{ background: #dcfce7; color: #166534; }}
</style>
</head>
<body>
<h1>Verso User's Guide</h1>
<p>{stable_link}{latest_link}</p>
<h2>All versions</h2>
<ul>
{version_list}
</ul>
</body>
</html>
"""

    with open("index.html", "w", encoding="utf-8") as f:
        f.write(html)
    print("Generated root index.html")


def deploy_version(source_dir, version, commit_sha, branch):
    """
    Deploy a version by copying from source directory to versioned directory.

    Args:
        source_dir (str): Source directory to copy content from
        version (str): Version string (will be used as the directory name)
        commit_sha (str): Full SHA of the commit being deployed
        branch (str): Git branch to checkout
    """
    # Save current git commit to restore later
    current_commit = run_git_command(["git", "rev-parse", "HEAD"])

    try:
        # Copy source to a temp dir (needed because git switch will change the working tree)
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_source = os.path.join(temp_dir, "source_copy")
            shutil.copytree(source_dir, temp_source)
            print(f"Copied {source_dir} to temporary directory")

            # Switch to the deploy branch
            print(f"Checking out branch: {branch}")
            run_git_command(["git", "switch", "-c", branch, "--track", "origin/" + branch])

            # Remove existing version directory if it exists
            version_dir = version
            if os.path.exists(version_dir):
                print(f"Removing existing version directory: {version_dir}")
                shutil.rmtree(version_dir)

            # Copy from temp to version directory, then stamp in place
            print(f"Copying content to version directory: {version_dir}")
            shutil.copytree(temp_source, version_dir)
            print(f"Stamping HTML files with commit {commit_sha}")
            stamp_html_files(version_dir, commit_sha)

            run_git_command(["git", "add", version_dir])

            # Update the "latest" pointer if needed
            latest_version = find_latest_version(".")

            if latest_version:
                if os.path.islink("latest"):
                    os.unlink("latest")
                if os.path.isdir("latest"):
                    shutil.rmtree("latest", ignore_errors=True)

                shutil.copytree(latest_version, "latest")
                print(f"Updated 'latest' alias as a copy of: {latest_version}")
                run_git_command(["git", "add", "latest"])

            # Update the "stable" pointer if needed
            latest_stable_version = find_latest_stable_version(".")

            if latest_stable_version:
                if os.path.islink("stable"):
                    os.unlink("stable")
                if os.path.isdir("stable"):
                    shutil.rmtree("stable", ignore_errors=True)

                shutil.copytree(latest_stable_version, "stable")
                print(f"Updated 'stable' alias as a copy of: {latest_stable_version}")
                run_git_command(["git", "add", "stable"])

            # Generate root index.html
            generate_index_html(latest_version, latest_stable_version)
            run_git_command(["git", "add", "index.html"])

            if git_has_changes():
                run_git_command(["git", "commit", "-m", f"Deploy {version}"])
            else:
                print("Nothing changed, so no commit will be made.")

    finally:
        # Restore the original branch
        print(f"Restoring original commit: {current_commit}")
        run_git_command(["git", "switch", "--detach", current_commit])

    print(f"Deployment of version {version} completed successfully.")


def main():
    parser = argparse.ArgumentParser(
        description="Deploy built HTML to the deployment branch"
    )
    parser.add_argument("source_dir", help="Source directory containing built HTML")
    parser.add_argument("version", help="Version string (e.g., 4.29.0)")
    parser.add_argument("commit_sha", help="Full SHA of the commit being deployed")
    parser.add_argument("branch", help="Git branch for deployment")

    args = parser.parse_args()

    print(f"Deploying from {args.source_dir} as version {args.version} into {args.branch}")

    deploy_version(args.source_dir, args.version, args.commit_sha, args.branch)


if __name__ == "__main__":
    main()
