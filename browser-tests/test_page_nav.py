from playwright.sync_api import Page, expect


def nav_link(page: Page, rel: str):
    return page.locator(f'.prev-next-buttons a[rel="{rel}"]').first


def open_second_page(page: Page, server: str) -> str:
    """Opens the page after the front page, which has both a previous and a next page."""
    page.goto(f"{server}/")
    page.wait_for_load_state("networkidle")
    next_href = nav_link(page, "next").evaluate("a => a.href")
    page.goto(next_href)
    page.wait_for_load_state("networkidle")
    return page.url


class TestPageNav:
    def test_links_advertise_shortcuts(self, server: str, page: Page):
        """The previous and next links name the keys that follow them."""
        open_second_page(page, server)
        expect(nav_link(page, "prev")).to_have_attribute(
            "aria-keyshortcuts", "ArrowLeft"
        )
        expect(nav_link(page, "next")).to_have_attribute(
            "aria-keyshortcuts", "ArrowRight"
        )

    def test_arrow_keys_follow_links(self, server: str, page: Page):
        """ArrowRight goes to the next page and ArrowLeft to the previous one."""
        start = open_second_page(page, server)
        next_href = nav_link(page, "next").evaluate("a => a.href")
        prev_href = nav_link(page, "prev").evaluate("a => a.href")

        page.keyboard.press("ArrowRight")
        page.wait_for_url(next_href)

        page.goto(start)
        page.wait_for_load_state("networkidle")
        page.keyboard.press("ArrowLeft")
        page.wait_for_url(prev_href)

    def test_modified_arrow_keys_are_ignored(self, server: str, page: Page):
        """Arrow keys with a modifier are left to the browser."""
        start = open_second_page(page, server)
        page.keyboard.press("Shift+ArrowRight")
        page.keyboard.press("Shift+ArrowLeft")
        page.wait_for_timeout(300)
        assert page.url == start

    def test_arrow_keys_in_search_box_are_ignored(self, server: str, page: Page):
        """Arrow keys move the caret in the search box instead of changing pages."""
        start = open_second_page(page, server)
        searchbox = page.get_by_role("searchbox")
        searchbox.click()
        searchbox.type("abc")
        page.keyboard.press("ArrowLeft")
        page.keyboard.press("ArrowRight")
        page.wait_for_timeout(300)
        assert page.url == start
