import pytest
from content_security_policy_checks import (
    assert_injected_inline_script_blocked,
    assert_markers_set,
    assert_policy_precedes_scripts,
)
from playwright.sync_api import Page, expect

# The landing page, a module page with code hovers, and the search page. Each one is built by a
# different function of literate-html, and each one gets its own policy.
PAGES = ["/", "/LitConfig/Core/", "/search/?q=hello"]

# The extra script source from `test-projects/literate-config/literate.toml`.
EXTRA_SOURCE = "https://scripts.example.com:8443"

# The marker that `test-projects/literate-config/scripts/extra-script-marker.js` sets.
EXTRA_SCRIPT_MARKER = "literateExtraScriptMarker"


# The sources of the `script-src` directive of a page's policy.
def script_sources(page: Page):
    policy = page.locator('meta[http-equiv="Content-Security-Policy"]').get_attribute(
        "content"
    )
    for directive in policy.split(";"):
        name, *sources = directive.split()
        if name == "script-src":
            return sources
    return []


def load(page: Page, server: str, path: str):
    page.goto(f"{server}{path}")
    page.wait_for_load_state("networkidle")


@pytest.mark.parametrize("path", PAGES)
def test_policy_precedes_scripts_and_base(server: str, page: Page, path: str):
    load(page, server, path)
    assert_policy_precedes_scripts(page)


# The extra script from `extra_js` runs on every page, and the configured extra source is part of
# every page's policy. The `page` fixture fails the test if any of the page's own scripts is
# blocked.
@pytest.mark.parametrize("path", PAGES)
def test_configured_scripts_run(server: str, page: Page, path: str):
    load(page, server, path)
    assert_markers_set(page, [EXTRA_SCRIPT_MARKER])
    assert EXTRA_SOURCE in script_sources(page)


# Hovers depend on the inline highlighting script, which runs only when its hash is in the policy.
def test_hovers_work(server: str, page: Page):
    load(page, server, "/LitConfig/Core/")
    token = page.locator(".hl.lean .const.token").first
    expect(token).to_be_visible()
    token.hover()
    page.wait_for_function(
        "el => !!el._tippy", arg=token.element_handle(), timeout=5000
    )
    expect(page.locator(".tippy-box").first).to_be_visible()


# The search page renders its results with module scripts from the site's own origin, so the
# results appear only when the policy allows those scripts.
def test_search_page_scripts_run(server: str, page: Page):
    load(page, server, "/search/?q=hello")
    expect(page.locator(".search-page-host .search-page-input")).to_have_value("hello")
    expect(page.locator("ul.search-page-list li").first).to_be_visible()


# A script that is added after the page loads has no hash in the policy, so the browser blocks
# it. This shows that the policy is enforced and not only present.
@pytest.mark.parametrize("path", PAGES)
def test_injected_inline_script_is_blocked(
    server: str, page: Page, content_security_policy_violations, path: str
):
    load(page, server, path)
    assert_injected_inline_script_blocked(page, content_security_policy_violations)
