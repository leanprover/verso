from playwright.sync_api import expect, Page


class TestMultiRootNavigation:
    """Tests for navigation in a multi-root project (no nav flattening)."""

    def test_multi_root_no_nav_title(self, server: str, page: Page):
        """Test that a multi-root site does not use nav-title."""
        page.goto(f"{server}/LibA/")
        page.wait_for_load_state("networkidle")

        nav = page.locator("nav.module-tree")
        nav_title = nav.locator(".nav-title")
        expect(nav_title).to_have_count(0)

    def test_multi_root_uses_details(self, server: str, page: Page):
        """Test that top-level entries use collapsible <details> elements."""
        page.goto(f"{server}/LibA/")
        page.wait_for_load_state("networkidle")

        nav = page.locator("nav.module-tree")

        # Should have <details> for both LibA and LibB at top level
        top_details = nav.locator(":scope > details")
        assert top_details.count() >= 2, (
            f"Expected at least 2 top-level <details>, got {top_details.count()}"
        )

        nav_text = nav.inner_text()
        assert "LibA" in nav_text, f"Expected 'LibA' in navbar"
        assert "LibB" in nav_text, f"Expected 'LibB' in navbar"

    def test_multi_root_children_indented(self, server: str, page: Page):
        """Test that child entries in multi-root nav are indented inside details."""
        page.goto(f"{server}/LibA/")
        page.wait_for_load_state("networkidle")

        nav = page.locator("nav.module-tree")

        # Top-level <details> should have margin-left from .module-tree details rule
        top_details = nav.locator(":scope > details").first
        margin = top_details.evaluate("el => getComputedStyle(el).marginLeft")
        assert margin == "0px", (
            f"Expected top-level details margin-left to be '0px', got '{margin}'"
        )

        # Nested details (or leaves) inside a top-level details should be indented
        nested = top_details.locator("details, .leaf").first
        nested_margin = nested.evaluate("el => getComputedStyle(el).marginLeft")
        assert nested_margin != "0px", (
            f"Expected nested element to be indented, got margin-left '{nested_margin}'"
        )
