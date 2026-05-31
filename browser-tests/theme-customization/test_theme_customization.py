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
    # ManualTheme additions (chrome).
    "headerBackground": "#001b1b",
    "tocBackground": "#001c1c",
    "linkColor": "#002020",
    "tocTextColor": "#002222",
    "borderColor": "#001d1d",
    "mutedColor": "#001e1e",
    "highlightColor": "#001f1f",
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
    assert actual == expected, (
        f"{description}: expected {expected} ({hex_value}), got {actual}"
    )


def test_token_colors(page):
    # The first `.keyword` in the only code block is `def`.
    _expect(
        _color(page, "code.hl.lean .keyword"), THEME["keywordColor"], "keyword color"
    )
    # `.const` on `hello` (the function name) and `String` (the type).
    _expect(_color(page, "code.hl.lean .const"), THEME["constColor"], "const color")
    # `.var` on `name` (the parameter binding).
    _expect(_color(page, "code.hl.lean .var"), THEME["varColor"], "var color")
    # `.unknown` (operator-like tokens) falls back to `--verso-code-color`.
    _expect(
        _color(page, "code.hl.lean .unknown"), THEME["codeColor"], "fallback code color"
    )


def _goto_diagnostics(page, server):
    page.goto(server + "/Diagnostics/")


def test_error_indicator(page, server):
    _goto_diagnostics(page, server)
    _expect(
        _color(page, "pre.lean-output.error", "border-left-color"),
        THEME["errorIndicatorColor"],
        "lean-output.error indicator border",
    )


def test_page_background(page):
    _expect(
        _color(page, "body", "background-color"), THEME["background"], "body background"
    )


def test_body_text_color(page):
    # `body` now sets `color: var(--verso-text-color)`. Inherited text in prose elements
    # (paragraphs in `main`) should resolve to the theme's textColor rather than the
    # browser-default black.
    _expect(_color(page, "main p"), THEME["textColor"], "body prose color")


def test_header_background(page):
    _expect(
        _color(page, "header", "background-color"),
        THEME["headerBackground"],
        "header background",
    )


def test_header_title_color(page):
    # `.header-title` previously hardcoded `color: black`; the theme's `textColor` is now what
    # the rendered title actually uses, so a theme with textColor != black is readable on
    # a non-white header background.
    _expect(
        _color(page, ".header-title"),
        THEME["textColor"],
        "header title color",
    )


def test_toc_background_and_link_color(page):
    _expect(
        _color(page, "#toc", "background-color"),
        THEME["tocBackground"],
        "toc background",
    )
    # `#toc a` previously hardcoded `color: #333`; the theme's `tocTextColor` is now used,
    # so a dark ToC background plus a light tocTextColor stays readable.
    _expect(
        _color(page, "#toc a"),
        THEME["tocTextColor"],
        "toc link color",
    )


def test_content_link_color(page, server):
    # The doc has an `<a href="https://example.com/">` content link inside `main`. The new
    # `main a { color: var(--verso-link-color) }` rule should pick up the theme's linkColor.
    page.goto(server + "/Code-samples/")
    _expect(
        _color(page, 'main a[href^="https://example.com"]'),
        THEME["linkColor"],
        "content link color",
    )


def _root_var(page, name: str) -> str:
    """Resolves a CSS custom property at the document-root level to its computed `rgb(...)`."""
    return page.evaluate(
        "(name) => {"
        "  const raw = getComputedStyle(document.documentElement).getPropertyValue(name).trim();"
        "  if (raw.startsWith('rgb')) return raw;"
        "  const probe = document.createElement('span');"
        "  probe.style.color = raw;"
        "  document.body.appendChild(probe);"
        "  const out = getComputedStyle(probe).color;"
        "  probe.remove();"
        "  return out;"
        "}",
        name,
    ).strip()


def test_border_var(page):
    # `borderColor` is the search-input border color (and other chrome borders); the search box
    # is mounted by JS so the variable is the most direct verification that the theme value
    # reaches the page. (The CSS rules in search-box.css / search-page.css use
    # `var(--verso-border-color, gray)` so a missing variable would fall back to gray.)
    _expect(
        _root_var(page, "--verso-border-color"), THEME["borderColor"], "borderColor var"
    )


def test_prev_next_nav_color(page, server):
    # The `.prev-next-buttons > *` rule previously hardcoded `color: black`. It now reads
    # `var(--verso-text-color)` — section navigation is body-text colored, not link-colored,
    # so it stays readable on any themed background without competing with content links.
    # Both `:link` and `:visited` must land on text color; the visited-link rule for `main a`
    # has higher specificity than `.prev-next-buttons > *` and would otherwise paint visited
    # prev/next links in the visited-link color.
    page.goto(server + "/Code-samples/")
    # Force the prev page into the visited-link state by navigating to it once and back.
    page.evaluate("history.replaceState({}, '', '/Diagnostics/')")
    page.goto(server + "/Diagnostics/")
    page.goto(server + "/Code-samples/")
    colors = page.evaluate(
        """() => {
            const links = Array.from(document.querySelectorAll('.prev-next-buttons > a'));
            return links.map(a => getComputedStyle(a).color);
        }"""
    )
    expected = _hex_to_rgb(THEME["textColor"])
    assert colors and all(c == expected for c in colors), (
        f"all prev/next links should be {expected}; got {colors}"
    )


def test_search_placeholder_muted(page, server):
    # The quick-search placeholder previously hardcoded `#888` and the "more results" row `#777`.
    # Both now route through `--verso-muted-color`. The search box itself is mounted by JS;
    # waiting for the placeholder text confirms the rule reaches a real rendered element.
    page.goto(server + "/Code-samples/")
    placeholder = page.locator("#search-wrapper .cb_edit:empty").first
    placeholder.wait_for(state="attached", timeout=10000)
    color = page.evaluate(
        "() => getComputedStyle(document.querySelector('#search-wrapper .cb_edit:empty'),"
        " '::before').getPropertyValue('color')"
    ).strip()
    _expect(color, THEME["mutedColor"], "search placeholder color")


def test_search_match_highlight(page, server):
    # Full-page search results render each matched term inside an `<em>`, whose background
    # comes from `--verso-highlight-color` via `search-page.css`. Driving an actual search
    # confirms a rendered match `<em>` consumes the theme value (root variable existence is
    # not enough; the CSS rule has to actually read it).
    page.goto(server + "/search/?q=hello")
    em = page.locator(".search-page-list li.search-result em").first
    em.wait_for(state="attached", timeout=10000)
    _expect(
        _color(page, ".search-page-list li.search-result em", "background-color"),
        THEME["highlightColor"],
        "search-result match highlight",
    )
