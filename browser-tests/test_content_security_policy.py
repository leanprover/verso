import pytest
from conftest import load_redirects
from content_security_policy_checks import (
    assert_injected_inline_script_blocked,
    assert_policy_precedes_scripts,
)
from playwright.sync_api import Page


def content_page_path():
    for _, target in load_redirects():
        address = target.split("#")[0]
        if address.strip("/"):
            return "/" + address.strip("/") + "/"
    raise AssertionError("the users guide has no content page below the front page")


def find_page_path():
    name, _ = load_redirects()[0]
    return f"/find/?domain=Verso.Genre.Manual.section&name={name}"


# Each kind of page that the manual writes. The find page stays put for a name that it can't
# find, so that its own policy can be checked.
PAGES = {
    "front": lambda: "/",
    "content": content_page_path,
    "search": lambda: "/search/?q=manual",
    "find": lambda: "/find/?domain=Verso.Genre.Manual.section&name=no-such-name",
}


@pytest.fixture(params=PAGES.keys())
def loaded_page(request, server: str, page: Page):
    page.goto(server + PAGES[request.param]())
    page.wait_for_load_state("networkidle")
    return page


class TestContentSecurityPolicy:
    # The `page` fixture fails the test if any of the page's own scripts is blocked.
    def test_policy_precedes_scripts(self, loaded_page: Page):
        assert_policy_precedes_scripts(loaded_page)

    def test_injected_inline_script_is_blocked(
        self, loaded_page: Page, content_security_policy_violations
    ):
        assert_injected_inline_script_blocked(
            loaded_page, content_security_policy_violations
        )

    # The find page's inline script holds the cross-reference data, so a redirect to a permalink
    # target shows that the script ran.
    def test_find_page_redirects(self, server: str, page: Page):
        page.goto(server + find_page_path())
        page.wait_for_url(lambda url: "/find/" not in url)
        page.wait_for_load_state("networkidle")
        assert_policy_precedes_scripts(page)
