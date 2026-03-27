import re

from playwright.sync_api import expect, Page


class TestSearch:
    """Tests for search box, results, navigation, keyboard interaction, and ARIA."""

    def test_search_box_present(self, server: str, page: Page):
        """Test that role="searchbox" is visible and focusable."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        searchbox = page.get_by_role("searchbox")
        expect(searchbox).to_be_visible()
        searchbox.focus()
        expect(searchbox).to_be_focused()

    def test_search_finds_results(self, server: str, page: Page):
        """Test that typing a definition name shows results."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        searchbox = page.get_by_role("searchbox")
        searchbox.focus()
        searchbox.type("hello", delay=50)

        # Wait for results to appear
        results = page.locator('[role="listbox"]')
        expect(results).to_be_visible()

        options = results.locator('[role="option"]')
        assert options.count() >= 1, "Expected at least one search result for 'hello'"

    def test_search_result_navigates(self, server: str, page: Page):
        """Test that clicking a search result goes to the correct page."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        searchbox = page.get_by_role("searchbox")
        searchbox.focus()
        searchbox.type("double", delay=50)

        results = page.locator('[role="listbox"]')
        expect(results).to_be_visible()

        # Click the first result
        first_result = results.locator('[role="option"]').first
        expect(first_result).to_be_visible()
        first_result.click()
        page.wait_for_load_state("networkidle")

        # Should have navigated away from the current page
        url = page.url
        assert url != f"{server}/LitConfig/", f"Expected navigation from search result, still at {url}"

    def test_search_no_results(self, server: str, page: Page):
        """Test that gibberish query shows no results."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        searchbox = page.get_by_role("searchbox")
        searchbox.focus()
        searchbox.type("xyzzyqwert", delay=50)

        # The listbox should either stay hidden or appear with no options.
        # First type a real query to trigger the search UI, then clear and
        # type gibberish — but since we typed gibberish directly, just
        # verify the listbox either never appears or has no options.
        results = page.locator('[role="listbox"]')
        options = results.locator('[role="option"]')
        # Use expect with auto-retry: after search processes, there should be 0 options
        expect(options).to_have_count(0)

    def test_search_keyboard(self, server: str, page: Page):
        """Test arrow keys move selection and Escape closes results."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        searchbox = page.get_by_role("searchbox")
        searchbox.focus()
        searchbox.type("double", delay=50)

        results = page.locator('[role="listbox"]')
        expect(results).to_be_visible()

        # Wait for at least one option to be available
        first_option = results.locator('[role="option"]').first
        expect(first_option).to_be_visible()

        # Arrow down should select a result - verify by checking aria-selected
        page.keyboard.press("ArrowDown")

        # The selected option should have aria-selected="true"
        selected = results.locator('[aria-selected="true"]')
        expect(selected).to_have_count(1)

        # Escape should close the results
        page.keyboard.press("Escape")
        expect(results).not_to_be_visible()

    def test_search_keyboard_enter(self, server: str, page: Page):
        """Test that pressing Enter on a selected result navigates or closes results."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        searchbox = page.get_by_role("searchbox")
        searchbox.focus()
        searchbox.type("double", delay=50)

        results = page.locator('[role="listbox"]')
        expect(results).to_be_visible()

        # Wait for first option
        first_option = results.locator('[role="option"]').first
        expect(first_option).to_be_visible()

        # Select first result with arrow down, then press Enter
        page.keyboard.press("ArrowDown")
        selected = results.locator('[aria-selected="true"]')
        expect(selected).to_have_count(1)

        original_url = page.url
        page.keyboard.press("Enter")

        # Enter should either navigate to a new page or at least close the results.
        # Use expect with auto-retry instead of a fixed timeout.
        expect(page).not_to_have_url(original_url)

    def test_search_aria(self, server: str, page: Page):
        """Test ARIA attributes on search: autocomplete, expanded, controls, listbox, option."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        searchbox = page.get_by_role("searchbox")
        expect(searchbox).to_have_attribute("aria-autocomplete", "list")
        expect(searchbox).to_have_attribute("aria-expanded", "false")
        expect(searchbox).to_have_attribute("aria-controls", re.compile(r".+"))
        expect(searchbox).to_have_attribute("aria-haspopup", "listbox")

        # Type to trigger results
        searchbox.focus()
        searchbox.type("hello", delay=50)

        results = page.locator('[role="listbox"]')
        expect(results).to_be_visible()

        # Expanded should now be true
        expect(searchbox).to_have_attribute("aria-expanded", "true")

        # Results should have role="listbox" with aria-label
        expect(results).to_have_attribute("aria-label", re.compile(r".+"))

        # Each result should have role="option"
        options = results.locator('[role="option"]')
        assert options.count() >= 1
