"""Shared accessibility regression tests for the full-page search view.

Each genre's `test_search_page.py` subclasses `SearchPageAccessibilityBase` with a
genre-appropriate `QUERY` (one that yields at least one result in that genre's test
corpus). The test bodies themselves are genre-independent — they exercise the shared
`search-page.js` / `search-page.css` contract.

These are the accessibility gaps identified in the PR #847 review; they're expected to
fail until each gap is fixed.
"""

from playwright.sync_api import Page, expect


class SearchPageAccessibilityBase:
    """Mixin-style base; concrete test classes set `QUERY` to a term with results."""

    QUERY: str = ""

    def test_results_list_has_listbox_role(self, server: str, page: Page):
        """The result `<ul>` should carry `role="listbox"` so the `role="option"` children
        emitted by `renderCandidateLi` aren't orphaned from an a11y tree perspective."""
        page.goto(f"{server}/search/?q={self.QUERY}")
        page.wait_for_load_state("networkidle")
        page.wait_for_function(
            "document.querySelectorAll('ul.search-page-list li').length > 0",
            timeout=5_000,
        )
        expect(page.locator("ul.search-page-list")).to_have_attribute("role", "listbox")

    def test_count_element_is_aria_live(self, server: str, page: Page):
        """The result count should be an `aria-live` region so screen reader users hear
        the new count when the query changes."""
        page.goto(f"{server}/search/?q={self.QUERY}")
        page.wait_for_load_state("networkidle")
        live = page.locator("#search-page-count").get_attribute("aria-live")
        assert live in ("polite", "assertive"), (
            f"expected aria-live=polite|assertive on #search-page-count, got {live!r}"
        )

    def test_result_is_keyboard_focusable(self, server: str, page: Page):
        """Each result should be reachable by keyboard — either the `<li>` is focusable
        (non-negative tabindex) or it contains a natively focusable element
        (`<a href>`, `<button>`)."""
        page.goto(f"{server}/search/?q={self.QUERY}")
        page.wait_for_load_state("networkidle")
        page.wait_for_function(
            "document.querySelectorAll('ul.search-page-list li').length > 0",
            timeout=5_000,
        )
        is_focusable = page.locator("ul.search-page-list li").first.evaluate(
            """el => {
                const check = (e) => {
                    const ti = e.getAttribute('tabindex');
                    if (ti !== null && parseInt(ti, 10) >= 0) return true;
                    if ((e.tagName === 'A' && e.hasAttribute('href'))
                        || (e.tagName === 'BUTTON' && !e.hasAttribute('disabled'))) return true;
                    return false;
                };
                return check(el) || Array.from(el.querySelectorAll('*')).some(check);
            }"""
        )
        assert is_focusable, "search result is not reachable via keyboard"

    def test_enter_on_focused_result_navigates(self, server: str, page: Page):
        """Pressing Enter on a focused result should navigate to it. Uses Playwright's
        `locator.press`, which focuses + presses atomically and delivers a trusted
        keyboard event — equivalent to a real keyboard user pressing Enter after
        tabbing onto the result."""
        page.goto(f"{server}/search/?q={self.QUERY}")
        page.wait_for_load_state("networkidle")
        page.wait_for_function(
            "document.querySelectorAll('ul.search-page-list li').length > 0",
            timeout=5_000,
        )
        first_result = page.locator("ul.search-page-list li").first
        focusable = first_result.locator("a[href], button, [tabindex]:not([tabindex='-1'])").first
        focusable.press("Enter")
        page.wait_for_load_state("networkidle")
        assert "/search/" not in page.url, (
            f"Enter on focused result should navigate away from /search/, got {page.url}"
        )

    def test_result_exposes_target_href(self, server: str, page: Page):
        """Results should expose their target URL as an `<a href>` so middle-click and
        open-in-new-tab work. Currently navigation happens via a `click` handler calling
        `window.location.assign`, which is keyboard- and right-click-hostile."""
        page.goto(f"{server}/search/?q={self.QUERY}")
        page.wait_for_load_state("networkidle")
        page.wait_for_function(
            "document.querySelectorAll('ul.search-page-list li').length > 0",
            timeout=5_000,
        )
        first_result = page.locator("ul.search-page-list li").first
        anchors = first_result.locator("a[href]")
        assert anchors.count() >= 1, "first result should contain an <a href=...> for navigation"
        href = anchors.first.get_attribute("href") or ""
        assert href.strip() and href.strip() != "#", (
            f"first result's <a href> should be a real URL, got {href!r}"
        )
