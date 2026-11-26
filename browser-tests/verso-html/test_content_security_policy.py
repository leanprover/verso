import pytest
from content_security_policy_checks import (
    assert_injected_inline_script_blocked,
    assert_policy_precedes_scripts,
)
from playwright.sync_api import Page, expect

# The root module page, which is the site's entry point, a module page with code hovers, and the
# search page. Each one gets its own policy.
PAGES = ["/LitConfig/", "/LitConfig/Core/", "/search/?q=hello"]


def load(page: Page, server: str, path: str):
    page.goto(f"{server}{path}")
    page.wait_for_load_state("networkidle")


@pytest.mark.parametrize("path", PAGES)
def test_policy_precedes_scripts_and_base(server: str, page: Page, path: str):
    load(page, server, path)
    assert_policy_precedes_scripts(page)


# verso-html applies the default configuration, so the policy allows only the site's own scripts
# and the hashes of its inline scripts. The `page` fixture fails the test if any of the page's own
# scripts is blocked.
@pytest.mark.parametrize("path", PAGES)
def test_default_policy(server: str, page: Page, path: str):
    load(page, server, path)
    policy = page.locator('meta[http-equiv="Content-Security-Policy"]').get_attribute(
        "content"
    )
    script_source, base_uri = policy.split(";")
    name, self_source, *hashes = script_source.split()
    assert (name, self_source) == ("script-src", "'self'"), policy
    assert all(source.startswith("'sha256-") for source in hashes), policy
    assert base_uri.split() == ["base-uri", "'self'"], policy


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
