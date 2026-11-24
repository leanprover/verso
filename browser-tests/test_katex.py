from playwright.sync_api import expect, Page


class TestKaTeX:
    def test_katex_render(self, server: str, page: Page):
        """Test that the markup page contains at least one rendered KaTeX math."""
        page.goto(f"{server}/Verso-Markup")  # TODO: page with search widget

        # This selector is empirically observed to match KaTeX output:
        results = page.locator(".katex-html .katex-base")

        # Assert on results
        expect(results).not_to_have_count(0)  # At least one KaTeX element

    def test_katex_fonts_load(self, server: str, page: Page):
        """Test that every KaTeX font used by the rendered math loads successfully."""
        page.goto(f"{server}/Verso-Markup")
        expect(page.locator(".katex-html .katex-base").first).to_be_visible()

        # Font faces load lazily, so force the KaTeX ones and wait for them.
        statuses = page.evaluate(
            """async () => {
                const faces = [...document.fonts].filter((f) =>
                    f.family.startsWith("KaTeX_"),
                );
                await Promise.allSettled(faces.map((f) => f.load()));
                await document.fonts.ready;
                return faces.map((f) => [f.family, f.style, f.weight, f.status]);
            }"""
        )
        assert statuses, "no KaTeX font faces are declared"
        failed = [s for s in statuses if s[3] != "loaded"]
        assert not failed, f"KaTeX fonts that failed to load: {failed}"
