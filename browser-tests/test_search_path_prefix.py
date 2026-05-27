"""Regression tests for the search UI when the manual is served under a non-root path prefix.

The Verso-built manual is sometimes mounted at a sub-path (e.g. `/reference/`
on lean-lang.org). Search-result navigation must include that prefix.

Historically, `xref.json` stored each entry's `address` as an absolute path
starting with `/` (e.g. `/Foo/`). The browser resolves an `<a href="/Foo/">`
against the *origin*, ignoring the page's `<base href>`, so a click on a
result under `/reference/` would navigate to `/Foo/` and lose the prefix.

These tests serve the same `_out/html-multi` build, but symlinked under
`/reference/`, then exercise every navigation path the search UI exposes:

  1. Combobox + ArrowDown + Enter (keyboard confirm — was already correct,
     routes through `navigateBaseRelative`).
  2. Combobox click on a result anchor.
  3. The resolved `a.href` on a combobox result anchor — captures every
     browser-native open-in-new-tab variant (middle-click, Ctrl/Cmd-click,
     right-click → open in new tab, drag-to-tab) without having to drive
     each one individually.
  4. Full search-page (`/search/?q=...`) click on a result.
"""

import os
import socket
import subprocess
import tempfile
import time
from pathlib import Path

import pytest
from playwright.sync_api import Page, expect


PREFIX = "/reference"


def _find_free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


@pytest.fixture(scope="session")
def prefixed_server(request):
    """Serve the same built site as the `server` fixture, but mounted under `/reference/`.

    We create a fresh temporary directory, symlink the built site into
    `<tmp>/reference`, and point `python -m http.server` at the temp dir.
    The site files themselves are unmodified — only the URL space changes.
    """
    site_dir = request.config.getoption("--site-dir")
    site_dir = (Path(__file__).parent / site_dir).resolve()
    if not site_dir.is_dir():
        pytest.skip(f"built site not found at {site_dir}; run `lake build` first")

    tmp = tempfile.TemporaryDirectory()
    mount = Path(tmp.name) / "reference"
    os.symlink(site_dir, mount, target_is_directory=True)

    port = _find_free_port()
    proc = subprocess.Popen(
        ["python", "-m", "http.server", str(port), "--bind", "127.0.0.1"],
        cwd=tmp.name,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    time.sleep(1)
    try:
        yield f"http://127.0.0.1:{port}"
    finally:
        proc.terminate()
        proc.wait()
        tmp.cleanup()


def _open_landing(page: Page, prefixed_server: str) -> None:
    page.goto(f"{prefixed_server}{PREFIX}/")
    page.wait_for_load_state("networkidle")


def _first_result_link(page: Page):
    return page.get_by_label("Results").get_by_role("link").first


class TestSearchUnderPathPrefix:
    def test_base_href_carries_prefix(self, prefixed_server: str, page: Page):
        """Fixture sanity check: pages under the prefix have a `<base>` whose
        resolved URL ends at the prefix, not at the bare origin."""
        _open_landing(page, prefixed_server)
        base_href = page.evaluate("document.querySelector('base')?.href")
        assert base_href is not None, "expected <base> element on manual page"
        assert base_href.rstrip("/").endswith(PREFIX), (
            f"<base href> should anchor at {PREFIX}, got {base_href!r}"
        )

    def test_combobox_arrow_enter_keeps_prefix(self, prefixed_server: str, page: Page):
        """ArrowDown + Enter routes through `navigateBaseRelative`. This path
        was already correct before the fix; included so the matrix is complete."""
        _open_landing(page, prefixed_server)
        searchbox = page.get_by_role("searchbox")
        searchbox.focus()
        searchbox.type("Html.visitM", delay=20)
        expect(_first_result_link(page)).to_be_visible()
        searchbox.press("ArrowDown")
        searchbox.press("Enter")
        page.wait_for_load_state("networkidle")
        assert page.url.startswith(f"{prefixed_server}{PREFIX}/"), (
            f"expected URL under {prefixed_server}{PREFIX}/, got {page.url}"
        )

    def test_combobox_result_anchor_resolves_under_prefix(
        self, prefixed_server: str, page: Page
    ):
        """The resolved `a.href` on a combobox result must include the prefix.

        This is what every browser-native open-in-new-tab interaction uses
        (middle-click, Ctrl/Cmd-click, right-click → open in new tab,
        drag-to-tab), so asserting it once covers the whole class.

        Before the fix, the anchor's `href` attribute is an absolute path
        like `/Foo/`, which `a.href` resolves against the origin — giving
        `http://host/Foo/`, with the `/reference/` prefix missing.
        """
        _open_landing(page, prefixed_server)
        searchbox = page.get_by_role("searchbox")
        searchbox.focus()
        searchbox.type("Html.visitM", delay=20)

        link = _first_result_link(page)
        expect(link).to_be_visible()
        resolved = link.evaluate("a => a.href")
        raw = link.evaluate("a => a.getAttribute('href')")
        assert f"{PREFIX}/" in resolved, (
            f"resolved combobox anchor href should be under {PREFIX}/, "
            f"got href={raw!r} resolved={resolved!r}"
        )

    def test_combobox_click_keeps_prefix(self, prefixed_server: str, page: Page):
        """Clicking a combobox result navigates via the browser's native anchor
        handling. The destination URL must include the prefix."""
        _open_landing(page, prefixed_server)
        searchbox = page.get_by_role("searchbox")
        searchbox.focus()
        searchbox.type("Html.visitM", delay=20)

        link = _first_result_link(page)
        expect(link).to_be_visible()
        link.click()
        page.wait_for_load_state("networkidle")
        assert page.url.startswith(f"{prefixed_server}{PREFIX}/"), (
            f"expected URL under {prefixed_server}{PREFIX}/, got {page.url}"
        )

    def test_search_page_result_anchor_resolves_under_prefix(
        self, prefixed_server: str, page: Page
    ):
        """The full search-page view renders results via the same
        `candidateTargetUrl` code path. Its anchors must also resolve under
        the prefix."""
        page.goto(f"{prefixed_server}{PREFIX}/search/?q=Html")
        page.wait_for_load_state("networkidle")

        link = page.locator("ul.search-page-list li a").first
        expect(link).to_be_visible()
        resolved = link.evaluate("a => a.href")
        raw = link.evaluate("a => a.getAttribute('href')")
        assert f"{PREFIX}/" in resolved, (
            f"resolved search-page anchor href should be under {PREFIX}/, "
            f"got href={raw!r} resolved={resolved!r}"
        )

    def test_search_page_click_keeps_prefix(self, prefixed_server: str, page: Page):
        """Clicking a result on the full search page should land somewhere
        under the prefix and away from `/search/`."""
        page.goto(f"{prefixed_server}{PREFIX}/search/?q=Html")
        page.wait_for_load_state("networkidle")

        first = page.locator("ul.search-page-list li a").first
        expect(first).to_be_visible()
        first.click()
        page.wait_for_load_state("networkidle")
        assert page.url.startswith(f"{prefixed_server}{PREFIX}/"), (
            f"expected URL under {prefixed_server}{PREFIX}/, got {page.url}"
        )
        assert "/search/" not in page.url, (
            f"expected navigation away from /search/, got {page.url}"
        )
