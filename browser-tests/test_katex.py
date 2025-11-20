from playwright.sync_api import expect, Page

class TestKaTeX:
    def test_katex_render(self, server: str, page: Page):
        """Test that the markup page contains at least one rendered KaTeX math."""
        page.goto(f"{server}/Verso-Markup")  # TODO: page with search widget

        # This selector is empirically observed to match KaTeX output:
        results = page.locator(".katex-html .base")

        # Assert on results
        expect(results).not_to_have_count(0)  # At least one KaTeX element
