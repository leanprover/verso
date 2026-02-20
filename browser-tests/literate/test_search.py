from playwright.sync_api import expect, Page


class TestSearch:
    def test_search_box_exists(self, server: str, page: Page):
        """Test that the search box is present and focusable."""
        page.goto(f"{server}/LitConfig/")

        searchbox = page.get_by_role("searchbox")
        expect(searchbox).to_be_visible()
        searchbox.focus()
        expect(searchbox).to_be_focused()

    def test_search_finds_content(self, server: str, page: Page):
        """Test that typing in the search box produces results."""
        page.goto(f"{server}/LitConfig/")

        searchbox = page.get_by_role("searchbox")
        searchbox.type("hello")

        # Wait for search results to appear
        results = page.get_by_label("Results")
        expect(results).to_be_visible()
