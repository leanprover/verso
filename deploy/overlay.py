#!/usr/bin/env python3
import argparse
import json
import os
import re
import subprocess
from release_utils import (
    run_git_command,
    is_git_ancestor,
    find_latest_version,
    find_latest_stable_version,
)
from pathlib import Path
from urllib.parse import urlsplit
from extend_content_security_policy import extend_policy

UNICODE_INPUT_FILES = [
    "unicode-input.min.js",
    "unicode-input-component.min.js",
]

STATS_HTML_FILE = "stats.html"

SCRIPT_ELEMENT = re.compile(r"<script\b([^>]*)>(.*?)</script>", re.DOTALL)
SCRIPT_SOURCE = re.compile(r'\ssrc="([^"]*)"')

# The commit from which the permalink and search scripts are taken.
VERSO_SCRIPTS_REF = "72f606748cc5f4e1ce9f6d0b7abbd37cf767c9fd"

# The permalink and search scripts, as paths relative to static-web/.
VERSO_SCRIPT_FILES = {
    "find.js": "find.js",
    "search-highlight.js": "search/search-highlight.js",
    "search-box.js": "search/search-box.js",
}


def read_verso_scripts():
    """
    Read the permalink and search scripts at VERSO_SCRIPTS_REF.

    The commit is fetched from origin if the repository doesn't have it, as in a shallow checkout.

    Returns:
        dict: Map from filename to text content
    """
    has_ref = subprocess.run(
        ["git", "cat-file", "-e", f"{VERSO_SCRIPTS_REF}^{{commit}}"],
        capture_output=True,
    )
    if has_ref.returncode != 0:
        run_git_command(["git", "fetch", "--depth", "1", "origin", VERSO_SCRIPTS_REF])
    result = {}
    for filename, path in VERSO_SCRIPT_FILES.items():
        # run_git_command strips the output, which would drop the file's final newline
        shown = subprocess.run(
            ["git", "show", f"{VERSO_SCRIPTS_REF}:static-web/{path}"],
            capture_output=True,
            text=True,
            check=True,
        )
        result[filename] = shown.stdout
        print(f"overlay.py: read {path} at {VERSO_SCRIPTS_REF}")
    return result


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


def scripts_in(html):
    """
    Returns the inline script bodies and the origins of external scripts in a snippet of HTML.
    """
    bodies = []
    origins = []
    for attributes, body in SCRIPT_ELEMENT.findall(html):
        source = SCRIPT_SOURCE.search(attributes)
        if source is None:
            bodies.append(body)
        else:
            url = urlsplit(source.group(1))
            if url.netloc:
                origins.append(f"{url.scheme}://{url.netloc}" if url.scheme else url.netloc)
    return bodies, origins


def inject_stats_html(directory, stats_html_content, extensions=(".html", ".htm")):
    """
    Recursively walk through `directory`, find all HTML files,
    and insert stats_html_content as the last element of <head>.

    The Content Security Policy of each page is extended to allow the snippet's scripts.

    Args:
        directory (Path): The directory in which to recursively modify files
        stats_html_content (str): HTML content to inject before </head>
    """
    stats_scripts, stats_origins = scripts_in(stats_html_content)
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
                    new_content = extend_policy(
                        new_content, stats_scripts, stats_origins
                    )
                    with open(filepath, "w", encoding="utf-8") as f:
                        f.write(new_content)
                    print(f"Injected stats HTML: {filepath}")
                else:
                    print(f"Skipped stats HTML injection (no </head>): {filepath}")


def update_find_page(version_dir, find_js):
    """
    Replace the script in a version's find/index.html with the find.js at VERSO_SCRIPTS_REF.

    The page's cross-reference data is kept. Older pages declare it with `let xref`, and the
    updated page declares it as `window.xref`, which is where the current script reads it from.
    The page's Content Security Policy, if any, is extended to allow the new script.

    Args:
        version_dir (Path): The version's directory
        find_js (str): The contents of find.js, from read_verso_scripts
    """
    page = version_dir / "find" / "index.html"
    if not page.is_file():
        return
    content = page.read_text(encoding="utf-8")
    match = re.search(r"(?:let |window\.)xref = ", content)
    if match is None:
        print(f"No cross-reference data, skipping: {page}")
        return
    _, data_end = json.JSONDecoder().raw_decode(content, match.end())
    script_start = content.rfind("<script", 0, match.start())
    script_end = content.find("</script>", data_end)
    if script_start < 0 or script_end < 0:
        print(f"Unexpected find page layout, skipping: {page}")
        return
    body_start = content.index(">", script_start) + 1
    body = (
        content[body_start : match.start()]
        + "window.xref = "
        + content[match.end() : data_end]
        + ";\n"
        + find_js
        + "\n"
    )
    new_content = extend_policy(
        content[:body_start] + body + content[script_end:], [body]
    )
    page.write_text(new_content, encoding="utf-8")
    print(f"Updated: {page}")


# The search-result snippet rendering in search-box.js: the snippet callback in highlightTextResult.
SNIPPET_START = "const highlightedSnippets = limitedSnippets.map((snippet) => {"
SNIPPET_END = re.compile(r"return elem;\s*\}\);")


def snippet_code(search_box_js):
    """Returns the start and end of the snippet rendering code in search-box.js, if present."""
    start = search_box_js.find(SNIPPET_START)
    if start < 0 or search_box_js.find(SNIPPET_START, start + 1) >= 0:
        return None
    end = SNIPPET_END.search(search_box_js, start)
    if end is None:
        return None
    return start, end.end()


def update_search_scripts(version_dir, verso_scripts):
    """
    Update a version's search scripts to the versions at VERSO_SCRIPTS_REF.

    search-highlight.js is replaced. In search-box.js, the snippet rendering for search results is
    replaced, because the rest of the file depends on the version of the search index.

    Args:
        version_dir (Path): The version's directory
        verso_scripts (dict): Map from filename to text content, from read_verso_scripts
    """
    search_dir = version_dir / "-verso-search"
    highlight = search_dir / "search-highlight.js"
    if highlight.is_file():
        highlight.write_text(verso_scripts["search-highlight.js"], encoding="utf-8")
        print(f"Replaced: {highlight}")

    box = search_dir / "search-box.js"
    if box.is_file():
        current = verso_scripts["search-box.js"]
        new_range = snippet_code(current)
        if new_range is None:
            raise Exception(
                f"Snippet rendering not found in search-box.js at {VERSO_SCRIPTS_REF}"
            )
        content = box.read_text(encoding="utf-8")
        old_range = snippet_code(content)
        if old_range is None:
            print(f"Snippet rendering not found, skipping: {box}")
            return
        new_content = (
            content[: old_range[0]]
            + current[new_range[0] : new_range[1]]
            + content[old_range[1] :]
        )
        box.write_text(new_content, encoding="utf-8")
        print(f"Updated: {box}")


# This function is the right thing to change to change the
# content of the overlays that are applied.
def apply_overlays(
    deploy_dir, unicode_input_files=None, stats_html_content=None, verso_scripts=None
):
    """
    Apply desired overlays inside current directory.

    Args:
        deploy_dir (str): Directory containing all versions
        unicode_input_files (dict): Map from filename to bytes content, read
            from main before switching to the deploy branch. If None or empty,
            the Unicode input file replacement overlay is skipped.
        stats_html_content (str): Content of stats.html from main. If None,
            the stats HTML injection overlay is skipped.
        verso_scripts (dict): Map from filename to text content of the permalink
            and search scripts, from read_verso_scripts. If None, these scripts are left as
            they are.
    """
    latest_version = find_latest_version(deploy_dir)
    latest_stable_version = find_latest_stable_version(deploy_dir)
    print(f"overlay.py: the latest version is {latest_version}")
    print(f"overlay.py: the latest stable version is {latest_stable_version}")
    for inner in Path(deploy_dir).iterdir():
        # Check for index.html to identify version directories
        if inner.is_dir() and (inner / "index.html").is_file():
            if verso_scripts:
                update_find_page(inner, verso_scripts["find.js"])
                update_search_scripts(inner, verso_scripts)
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

    verso_scripts = read_verso_scripts()

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
        apply_overlays(
            deploy_dir, unicode_input_files, stats_html_content, verso_scripts
        )
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


# Run from deploy/ with:
#   python3 -B -c "import overlay; overlay.test()"
def test():
    import tempfile
    from extend_content_security_policy import script_hash

    stats = (
        '<script async src="https://stats.example/s.js"></script>\n'
        "<script>\n  track()\n</script>\n"
    )
    assert scripts_in(stats) == (["\n  track()\n"], ["https://stats.example"])
    assert scripts_in('<script src="//cdn.example/a.js"></script>') == ([], ["cdn.example"])
    assert scripts_in('<script src="local.js"></script>') == ([], [])

    meta = '<meta http-equiv="Content-Security-Policy" content="script-src \'self\'; base-uri \'self\'"/>'
    find_page = (
        f'<html><head><meta charset="UTF-8"/>{meta}</head><body>'
        '<script>let xref = {"a": 1};\nold()</script></body></html>'
    )
    with tempfile.TemporaryDirectory() as tmp:
        version = Path(tmp)
        (version / "find").mkdir()
        page = version / "find" / "index.html"
        page.write_text(find_page, encoding="utf-8")
        update_find_page(version, "find()")
        result = page.read_text(encoding="utf-8")
        body = 'window.xref = {"a": 1};\nfind()\n'
        assert f"<script>{body}</script>" in result, result
        assert script_hash(body) in result, result

        inject_stats_html(version, stats)
        result = page.read_text(encoding="utf-8")
        assert script_hash("\n  track()\n") in result, result
        assert "'self' https://stats.example 'sha256-" in result, result


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
