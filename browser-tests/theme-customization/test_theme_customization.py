"""
Browser test that pins a representative subset of themed CSS variables to their rendered DOM
values. The test currently exercises the four token color fields (keyword, const, var, fallback)
plus the error indicator border. Other themed fields are emitted to `verso-themes.css` but are
not all asserted here; expanding coverage is straightforward as more rendered features land in
the small test document.

Workflow:

1. Build the `theme-test-site` Lean exe, which renders a small Manual document with a
   customized `CodeTheme` whose every color field holds a distinct sentinel value.
2. Serve the resulting `_out/theme-test/html-multi` directory.
3. For each themed element in the generated HTML, read its computed style and assert it
   matches the sentinel hex value the Lean theme set for that field.

If the rendered color drifts from the Lean theme value, the theme pipeline
(`CodeTheme.cssVariables` -> generated `verso-themes.css` -> `highlightingStyle`
`var(--verso-*)` lookups) is broken end-to-end.
"""

import socket
import subprocess
import time
from pathlib import Path

import pytest
from playwright.sync_api import sync_playwright


HERE = Path(__file__).parent
REPO_ROOT = HERE.parent.parent
SITE_DIR = REPO_ROOT / "_out" / "theme-test" / "html-multi"


def _hex_to_rgb(h: str) -> str:
    h = h.lstrip("#")
    if len(h) == 3:
        h = "".join(c * 2 for c in h)
    r, g, b = (int(h[i : i + 2], 16) for i in (0, 2, 4))
    return f"rgb({r}, {g}, {b})"


# Sentinel colors mirroring `src/tests/ThemeTestMain.lean`.
THEME = {
    "background": "#000101",
    "codeBlockBackground": "#000202",
    "textColor": "#000303",
    "codeColor": "#000404",
    "selectedColor": "#000606",
    "infoIndicatorColor": "#000808",
    "warningIndicatorColor": "#000a0a",
    "errorIndicatorColor": "#000c0c",
    "hoverBackground": "#000d0d",
    "constColor": "#001717",
    "keywordColor": "#001818",
    "varColor": "#001919",
}


def _find_free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


@pytest.fixture(scope="module")
def built_site():
    """Rebuilds the customized-theme test site under `_out/theme-test`."""
    subprocess.check_call(
        ["lake", "build", "theme-test-site"],
        cwd=REPO_ROOT,
    )
    if SITE_DIR.exists():
        # Wipe so a stale build can't pass a renamed/deleted assertion.
        subprocess.check_call(["rm", "-rf", str(SITE_DIR.parent)], cwd=REPO_ROOT)
    subprocess.check_call(
        ["lake", "exe", "theme-test-site", "--output", "_out/theme-test"],
        cwd=REPO_ROOT,
    )
    assert SITE_DIR.exists(), f"Manual build did not produce {SITE_DIR}"
    return SITE_DIR


@pytest.fixture(scope="module")
def server(built_site):
    port = _find_free_port()
    proc = subprocess.Popen(
        ["python", "-m", "http.server", str(port), "--bind", "127.0.0.1"],
        cwd=built_site,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    time.sleep(0.5)
    try:
        yield f"http://127.0.0.1:{port}"
    finally:
        proc.terminate()
        proc.wait()


@pytest.fixture(scope="module")
def playwright_instance():
    with sync_playwright() as p:
        yield p


@pytest.fixture(scope="module", params=["chromium", "firefox"])
def page(request, playwright_instance, server):
    browser = getattr(playwright_instance, request.param).launch()
    page = browser.new_page()
    page.goto(server + "/Code-samples/")
    yield page
    browser.close()


def _color(page, selector: str, prop: str = "color") -> str:
    return page.evaluate(
        "([sel, p]) => getComputedStyle(document.querySelector(sel)).getPropertyValue(p)",
        [selector, prop],
    ).strip()


def _expect(actual: str, hex_value: str, description: str) -> None:
    expected = _hex_to_rgb(hex_value)
    assert actual == expected, f"{description}: expected {expected} ({hex_value}), got {actual}"


def test_token_colors(page):
    # The first `.keyword` in the only code block is `def`.
    _expect(_color(page, "code.hl.lean .keyword"), THEME["keywordColor"], "keyword color")
    # `.const` on `hello` (the function name) and `String` (the type).
    _expect(_color(page, "code.hl.lean .const"), THEME["constColor"], "const color")
    # `.var` on `name` (the parameter binding).
    _expect(_color(page, "code.hl.lean .var"), THEME["varColor"], "var color")
    # `.unknown` (operator-like tokens) falls back to `--verso-code-color`.
    _expect(_color(page, "code.hl.lean .unknown"), THEME["codeColor"], "fallback code color")


def _goto_diagnostics(page, server):
    page.goto(server + "/Diagnostics/")


def test_error_indicator(page, server):
    _goto_diagnostics(page, server)
    _expect(
        _color(page, "pre.lean-output.error", "border-left-color"),
        THEME["errorIndicatorColor"],
        "lean-output.error indicator border",
    )
