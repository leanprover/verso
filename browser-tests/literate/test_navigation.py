import re

from playwright.sync_api import expect, Page


class TestNavigation:
    """Tests for navigation structure, navbar, breadcrumbs, page ToC, and mobile."""

    def test_navbar_structure(self, server: str, page: Page):
        """Test that nav.module-tree exists with aria-label and contains all modules."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        nav = page.locator("nav.module-tree")
        expect(nav).to_be_visible()
        expect(nav).to_have_attribute("aria-label", "Module navigation")

        # Should contain links/entries for top-level modules visible in the nav
        nav_text = nav.inner_text()
        for mod in ["LitConfig", "Core", "NoDocstrings"]:
            assert mod in nav_text, f"Expected '{mod}' in navbar, got: {nav_text}"

        # Basic may be inside a collapsed <details> subtree under Core;
        # verify it exists as a link/text somewhere in the nav HTML
        nav_html = nav.inner_html()
        assert "Basic" in nav_html, f"Expected 'Basic' somewhere in navbar HTML"

    def test_navbar_expand_collapse(self, server: str, page: Page):
        """Test that <details> in navbar toggles open/closed on summary click."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        # Find a details element in the navbar
        details_els = page.locator("nav.module-tree details")
        assert details_els.count() >= 1, "Expected at least one <details> in navbar"

        first_details = details_els.first
        summary = first_details.locator(":scope > summary")

        # Record initial state
        was_open = first_details.evaluate("el => el.open")

        # Click to toggle
        summary.click()
        if was_open:
            expect(first_details).not_to_have_attribute("open", "")
        else:
            expect(first_details).to_have_attribute("open", "")

        # Click again to toggle back
        summary.click()
        if was_open:
            expect(first_details).to_have_attribute("open", "")
        else:
            expect(first_details).not_to_have_attribute("open", "")

    def test_navbar_links_navigate(self, server: str, page: Page):
        """Test that clicking a navbar link navigates to the correct page."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        # Find a link to Core in the navbar
        nav = page.locator("nav.module-tree")
        core_link = nav.locator("a").filter(has_text="Core").first
        expect(core_link).to_be_visible()

        core_link.click()
        page.wait_for_load_state("networkidle")

        expect(page).to_have_url(re.compile(r"/LitConfig/Core/?$"))

    def test_current_page_highlighted(self, server: str, page: Page):
        """Test that .current class is on the current page entry and changes on navigate."""
        page.goto(f"{server}/LitConfig/Core/")
        page.wait_for_load_state("networkidle")

        current = page.locator("nav.module-tree .current")
        expect(current).to_have_count(1)
        expect(current).to_contain_text("Core")

        # Navigate to a different page
        page.goto(f"{server}/LitConfig/NoDocstrings/")
        page.wait_for_load_state("networkidle")

        current = page.locator("nav.module-tree .current")
        expect(current).to_have_count(1)
        expect(current).to_contain_text("NoDocstrings")

    def test_breadcrumbs_structure(self, server: str, page: Page):
        """Test that ol.breadcrumbs[aria-label="Breadcrumb"] exists with correct segments."""
        page.goto(f"{server}/LitConfig/Core/Basic/")
        page.wait_for_load_state("networkidle")

        breadcrumbs = page.locator('ol.breadcrumbs[aria-label="Breadcrumb"]')
        expect(breadcrumbs).to_be_visible()

        items = breadcrumbs.locator("li")
        expect(items).to_have_count(3)

    def test_breadcrumbs_depth(self, server: str, page: Page):
        """Test breadcrumb depth: root has 1 segment, Core/Basic has 3."""
        # Root module page
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        breadcrumbs = page.locator("ol.breadcrumbs")
        root_items = breadcrumbs.locator("li")
        expect(root_items).to_have_count(1)

        # Deeply nested page
        page.goto(f"{server}/LitConfig/Core/Basic/")
        page.wait_for_load_state("networkidle")

        breadcrumbs = page.locator("ol.breadcrumbs")
        deep_items = breadcrumbs.locator("li")
        expect(deep_items).to_have_count(3)

    def test_breadcrumb_links(self, server: str, page: Page):
        """Test that clicking a breadcrumb navigates correctly."""
        page.goto(f"{server}/LitConfig/Core/Basic/")
        page.wait_for_load_state("networkidle")

        breadcrumbs = page.locator("ol.breadcrumbs")
        first_link = breadcrumbs.locator("a").first
        first_link.click()
        page.wait_for_load_state("networkidle")

        expect(page).to_have_url(re.compile(re.escape(f"{server}/LitConfig") + r"/?$"))

    def test_page_toc_with_headings(self, server: str, page: Page):
        """Test that pages with >=2 headings show .page-toc with anchor links."""
        # LitConfig has "# LitConfig: A Test Module" and "## Overview" = 2 headings
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        toc = page.locator("nav.page-toc")
        expect(toc).to_be_visible()
        expect(toc).to_have_attribute("aria-label", "Page table of contents")

        # Should have "On this page" title
        title = toc.locator(".page-toc-title")
        expect(title).to_contain_text("On this page")

        # Should have links with anchors (prefixed with page path due to <base> tag)
        links = toc.locator("a")
        assert links.count() >= 2, f"Expected at least 2 ToC links, got {links.count()}"
        href = links.first.get_attribute("href")
        assert href and "#" in href, f"Expected anchor link, got '{href}'"

    def test_page_toc_absent_few_headings(self, server: str, page: Page):
        """Test that pages with <2 headings do not show .page-toc."""
        # NoDocstrings has no module docstrings, so likely 0 or 1 heading
        # Basic has only "# Basic Definitions" = 1 heading
        page.goto(f"{server}/LitConfig/Core/Basic/")
        page.wait_for_load_state("networkidle")

        toc = page.locator("nav.page-toc")
        expect(toc).to_have_count(0)

    def test_page_toc_links(self, server: str, page: Page):
        """Test that clicking a ToC link stays on the same page and adds a hash."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        toc = page.locator("nav.page-toc")
        if toc.count() == 0:
            return

        # Click the first ToC link
        link = toc.locator("a").first
        link.click()

        # Should stay on the LitConfig page with a hash fragment
        expect(page).to_have_url(re.compile(r"/LitConfig/.*#"))

    def test_mobile_hamburger_open(self, server: str, page: Page):
        """Test that at 375x667 the hamburger is visible and clicking opens the sidebar."""
        page.set_viewport_size({"width": 375, "height": 667})
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        hamburger = page.locator("label.hamburger")
        expect(hamburger).to_be_visible()

        sidebar = page.locator("aside.sidebar")

        # Click hamburger to open sidebar
        hamburger.click()
        expect(sidebar).to_be_visible()

    def test_mobile_hamburger_close(self, server: str, page: Page):
        """Test that clicking hamburger again closes the sidebar."""
        page.set_viewport_size({"width": 375, "height": 667})
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        hamburger = page.locator("label.hamburger")

        # Open
        hamburger.click()
        sidebar = page.locator("aside.sidebar")
        expect(sidebar).to_be_visible()

        # Close
        hamburger.click()
        # After closing, sidebar should be offscreen (translateX(-100%))
        # The checkbox should be unchecked
        toggle = page.locator("#menu-toggle")
        expect(toggle).not_to_be_checked()

    def test_mobile_code_horizontal_scroll(self, server: str, page: Page):
        """Test that .code-box has overflow-x: auto at mobile viewport."""
        page.set_viewport_size({"width": 375, "height": 667})
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        code_box = page.locator(".code-box").first
        overflow_x = code_box.evaluate("el => getComputedStyle(el).overflowX")
        assert overflow_x in ("auto", "scroll"), (
            f"Expected code-box overflow-x to be 'auto' or 'scroll' at mobile, got '{overflow_x}'"
        )

    def test_mobile_page_toc_hidden(self, server: str, page: Page):
        """Test that .page-toc is not displayed at <=1024px."""
        page.set_viewport_size({"width": 1024, "height": 768})
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        toc = page.locator("nav.page-toc")
        if toc.count() > 0:
            expect(toc).not_to_be_visible()

    def test_mobile_search_accessible(self, server: str, page: Page):
        """Test that search box is visible and focusable at mobile viewport."""
        page.set_viewport_size({"width": 375, "height": 667})
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        searchbox = page.get_by_role("searchbox")
        expect(searchbox).to_be_visible()
        searchbox.focus()
        expect(searchbox).to_be_focused()
