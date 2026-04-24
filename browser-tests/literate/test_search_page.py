"""End-to-end tests for the full-page search results view, Literate HTML genre."""

from playwright.sync_api import Page, expect

from search_page_a11y import SearchPageAccessibilityBase


class TestSearchPageAccessibility(SearchPageAccessibilityBase):
    QUERY = "hello"


class TestSearchPage:
    def test_enter_navigates_to_search_page(self, server: str, page: Page):
        """Typing a query and pressing Enter (with no listbox selection) should land on
        `/search/?q=<query>`."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        searchbox = page.get_by_role("searchbox")
        searchbox.focus()
        searchbox.type("hello", delay=20)
        searchbox.press("Escape")
        searchbox.press("Enter")

        page.wait_for_load_state("networkidle")
        assert "/search/" in page.url, f"expected /search/ in URL, got {page.url}"
        assert "q=hello" in page.url, f"expected q=hello in URL, got {page.url}"

    def test_search_page_renders_results(self, server: str, page: Page):
        page.goto(f"{server}/search/?q=hello")
        page.wait_for_load_state("networkidle")

        inbody_box = page.locator(".search-page-host .search-page-input")
        expect(inbody_box).to_be_visible()
        expect(inbody_box).to_have_value("hello")

        results = page.locator("ul.search-page-list li")
        expect(results.first).to_be_visible()
        assert results.count() >= 1

    def test_search_field_is_not_combobox(self, server: str, page: Page):
        page.goto(f"{server}/search/?q=hello")
        page.wait_for_load_state("networkidle")

        inbody_box = page.locator(".search-page-host .search-page-input")
        expect(inbody_box).to_be_visible()
        inbody_box.focus()
        inbody_box.type("x", delay=30)

        # No listbox on this page at all: the results list is a plain `<ul>` of
        # `<li>`s, each wrapping an `<a href>`.
        assert page.locator("[role='listbox']").count() == 0
        assert page.locator(".combobox-list").count() == 0

    def test_result_count_visible_at_top(self, server: str, page: Page):
        page.goto(f"{server}/search/?q=hello")
        page.wait_for_load_state("networkidle")
        page.wait_for_function(
            "/\\d+ results?$/.test(document.getElementById('search-page-count')?.textContent ?? '')",
            timeout=5_000,
        )
        expect(page.locator("#search-page-count")).to_be_visible()

    def test_empty_query_shows_placeholder(self, server: str, page: Page):
        page.goto(f"{server}/search/")
        page.wait_for_load_state("networkidle")

        count = page.locator("#search-page-count")
        expect(count).to_be_visible()
        expect(count).to_have_text("Type a query in the search box to see results.")

    def test_click_result_navigates(self, server: str, page: Page):
        page.goto(f"{server}/search/?q=double")
        page.wait_for_load_state("networkidle")

        first_result = page.locator("ul.search-page-list li").first
        expect(first_result).to_be_visible()
        first_result.click()
        page.wait_for_load_state("networkidle")

        assert "/search/" not in page.url, f"expected navigation away from /search/, got {page.url}"

    def test_inbody_box_live_updates_results(self, server: str, page: Page):
        """Editing the in-body search field updates results in-place; URL is synced via
        history.replaceState (no reload)."""
        page.goto(f"{server}/search/?q=hello")
        page.wait_for_load_state("networkidle")

        inbody_box = page.locator(".search-page-host .search-page-input")
        expect(inbody_box).to_be_visible()

        page.evaluate("window.__noReload = true")
        inbody_box.focus()
        inbody_box.press("ControlOrMeta+a")
        inbody_box.press("Delete")
        inbody_box.type("double", delay=20)

        page.wait_for_function(
            "new URL(location.href).searchParams.get('q') === 'double'",
            timeout=5_000,
        )
        assert page.evaluate("window.__noReload") is True, "page reloaded on input"
