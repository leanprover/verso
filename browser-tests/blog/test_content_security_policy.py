import pytest
from content_security_policy_checks import assert_injected_inline_script_blocked
from playwright.sync_api import Page, expect

# Markers that the demo site's custom scripts set on `window` when they run. Every page has the
# theme's scripts. `versoTestExternalScript` comes from the script that the theme loads from the
# external origin.
THEME_MARKERS = [
    "versoTestThemeInlineScript",
    "versoTestThemeJsFile",
    "versoTestExternalScript",
]

# The about page uses a component that adds a header script.
COMPONENT_MARKERS = ["versoTestComponentHeaderJs", "versoTestShadowScript"]

# The front page, the about page with components and math, the blog index, a post, and a post
# with Lean code and hovers.
PAGES = {
    "": THEME_MARKERS,
    "about/": THEME_MARKERS + COMPONENT_MARKERS,
    "blog/": THEME_MARKERS,
    "blog/1900-1-1-first-post/": THEME_MARKERS,
    "blog/2024-1-15-conditional-expressions-in-lean/": THEME_MARKERS,
}

LEAN_PAGE = "blog/2024-1-15-conditional-expressions-in-lean/"
MATH_PAGE = "about/"

POLICY_POSITION = """() => {
  const policy = document.querySelector('meta[http-equiv="Content-Security-Policy"]');
  if (!policy) return { found: false };
  const later = (el) => !!(policy.compareDocumentPosition(el) & Node.DOCUMENT_POSITION_FOLLOWING);
  return {
    found: true,
    inHead: policy.parentElement === document.head,
    content: policy.content,
    earlier: [...document.querySelectorAll("script, base")]
      .filter((el) => !later(el))
      .map((el) => el.outerHTML.slice(0, 100)),
  };
}"""


def check_external_origin(policy, port):
    origin = f"http://localhost:{port}"
    sources = policy.split(";")[0].split()
    assert origin in sources, (
        f"the content security policy doesn't list {origin}. Build the demo site with "
        f"VERSO_TEST_EXTERNAL_SCRIPT_PORT={port} and run the tests with --port {port}."
    )


@pytest.mark.parametrize("path", PAGES)
def test_policy_precedes_scripts_and_base(
    server: str, page: Page, path: str, external_script_port: str
):
    page.goto(f"{server}/{path}")
    position = page.evaluate(POLICY_POSITION)
    assert position["found"], "the page has no content security policy"
    assert position["inHead"], "the content security policy is outside <head>"
    assert position["content"].startswith("script-src 'self'")
    check_external_origin(position["content"], external_script_port)
    assert not position["earlier"], (
        f"elements that precede the policy: {position['earlier']}"
    )


@pytest.mark.parametrize("path", PAGES)
def test_custom_scripts_run(
    server: str, page: Page, path: str, external_script_port: str
):
    page.goto(f"{server}/{path}")
    check_external_origin(
        page.locator('meta[http-equiv="Content-Security-Policy"]').get_attribute(
            "content"
        ),
        external_script_port,
    )
    for marker in PAGES[path]:
        page.wait_for_function(f"() => window.{marker} === true", timeout=5000)


def test_hovers(server: str, page: Page):
    page.goto(f"{server}/{LEAN_PAGE}")
    page.wait_for_load_state("load")
    token = page.locator(".hl.lean .const.token").first
    expect(token).to_be_visible()
    token.hover()
    expect(page.locator(".tippy-box").first).to_be_visible()


def test_katex(server: str, page: Page):
    page.goto(f"{server}/{MATH_PAGE}")
    expect(page.locator(".math .katex-html").first).to_be_visible()


def test_injected_inline_script_is_blocked(
    server: str, page: Page, content_security_policy_violations
):
    page.goto(f"{server}/")
    assert_injected_inline_script_blocked(page, content_security_policy_violations)
