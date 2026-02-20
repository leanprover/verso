import re

from playwright.sync_api import expect, Page


class TestNavigation:
    def test_navbar_present(self, server: str, page: Page):
        """Test that the navbar exists with correct structure and ARIA label."""
        page.goto(f"{server}/LitConfig/")

        nav = page.locator("nav.module-tree")
        expect(nav).to_be_visible()
        expect(nav).to_have_attribute("aria-label", "Module navigation")

    def test_navbar_expand_collapse(self, server: str, page: Page):
        """Test that tree nodes can be expanded and collapsed."""
        # Navigate to NoDocstrings page so LitConfig.Core subtree is collapsed
        page.goto(f"{server}/LitConfig/NoDocstrings/")

        closed_selector = "nav.module-tree details:not([open])"
        open_selector = "nav.module-tree details[open]"

        closed_before = page.locator(closed_selector).count()
        if closed_before > 0:
            # Open a closed node
            summary = page.locator(closed_selector).first.locator(":scope > summary")
            summary.click()
            # Now there should be fewer closed details
            expect(page.locator(closed_selector)).to_have_count(closed_before - 1)
        else:
            # All open; close one
            open_before = page.locator(open_selector).count()
            summary = page.locator(open_selector).last.locator(":scope > summary")
            summary.click()
            expect(page.locator(open_selector)).to_have_count(open_before - 1)

    def test_current_page_highlighted(self, server: str, page: Page):
        """Test that the current page is highlighted in the navbar."""
        page.goto(f"{server}/LitConfig/Core/")

        # The Core entry in the navbar should have the 'current' class
        current = page.locator("nav.module-tree .current")
        expect(current).to_have_count(1)

    def test_breadcrumbs(self, server: str, page: Page):
        """Test that breadcrumbs show the correct module hierarchy."""
        page.goto(f"{server}/LitConfig/Core/Basic/")

        breadcrumbs = page.locator("ol.breadcrumbs")
        expect(breadcrumbs).to_be_visible()

        # Should have segments for LitConfig, Core, Basic
        items = breadcrumbs.locator("li")
        expect(items).to_have_count(3)

    def test_breadcrumb_links_work(self, server: str, page: Page):
        """Test that clicking a breadcrumb navigates to the correct page."""
        page.goto(f"{server}/LitConfig/Core/Basic/")

        # Click the first breadcrumb link (should be LitConfig)
        breadcrumbs = page.locator("ol.breadcrumbs")
        first_link = breadcrumbs.locator("a").first
        first_link.click()

        # Should navigate to the LitConfig page (with or without trailing slash)
        expect(page).to_have_url(re.compile(re.escape(f"{server}/LitConfig") + r"/?$"))

    def test_mobile_hamburger(self, server: str, page: Page):
        """Test that the hamburger menu works at mobile viewport."""
        page.set_viewport_size({"width": 375, "height": 667})
        page.goto(f"{server}/LitConfig/")

        # The sidebar should be hidden initially on mobile
        sidebar = page.locator("aside.sidebar")

        # The hamburger label should be visible
        hamburger = page.locator("label.hamburger")
        expect(hamburger).to_be_visible()

        # Click the hamburger to show the sidebar
        hamburger.click()

        # The sidebar should now be visible
        expect(sidebar).to_be_visible()
