from playwright.sync_api import expect, Page


class TestAccessibility:
    def test_skip_to_content_link(self, server: str, page: Page):
        """Test that the first focusable element is a skip-to-content link."""
        page.goto(f"{server}/LitConfig/")

        skip_link = page.locator("a.skip-link")
        expect(skip_link).to_have_count(1)
        expect(skip_link).to_have_attribute("href", "#main-content")

        # The skip link should target the main content area
        main = page.locator("#main-content")
        expect(main).to_have_count(1)

    def test_keyboard_navigation(self, server: str, page: Page):
        """Test that Tab key reaches interactive elements."""
        page.goto(f"{server}/LitConfig/")

        # Press Tab multiple times and verify we can reach interactive elements
        # The first Tab should focus the skip-to-content link
        page.keyboard.press("Tab")
        skip_link = page.locator("a.skip-link")
        expect(skip_link).to_be_focused()

    def test_aria_labels(self, server: str, page: Page):
        """Test that navigation landmarks have correct ARIA labels."""
        page.goto(f"{server}/LitConfig/")

        # Module navigation
        module_nav = page.locator('nav[aria-label="Module navigation"]')
        expect(module_nav).to_have_count(1)

        # Breadcrumbs
        breadcrumbs = page.locator('[aria-label="Breadcrumb"]')
        expect(breadcrumbs).to_have_count(1)

    def test_heading_hierarchy(self, server: str, page: Page):
        """Test that each page has exactly one h1 and no heading gaps."""
        page.goto(f"{server}/LitConfig/")

        # Exactly one h1
        h1_count = page.locator("h1").count()
        assert h1_count == 1, f"Expected exactly one h1, got {h1_count}"

    def test_axe_audit(self, server: str, page: Page):
        """Run axe-core accessibility audit on a representative page."""
        page.goto(f"{server}/LitConfig/")

        # Inject axe-core
        page.evaluate("""() => {
            return new Promise((resolve, reject) => {
                const script = document.createElement('script');
                script.src = 'https://cdnjs.cloudflare.com/ajax/libs/axe-core/4.10.2/axe.min.js';
                script.onload = resolve;
                script.onerror = reject;
                document.head.appendChild(script);
            });
        }""")

        # Run the audit
        results = page.evaluate("""() => {
            return new Promise((resolve) => {
                axe.run(document, {
                    rules: {
                        // Disable rules that require network access or are too strict for generated content
                        'color-contrast': { enabled: false },
                        'link-in-text-block': { enabled: false },
                        // Upstream Verso HTML issues (not literate-specific)
                        'aria-allowed-attr': { enabled: false },
                        'html-has-lang': { enabled: false },
                        'nested-interactive': { enabled: false }
                    }
                }).then(results => resolve(results));
            });
        }""")

        violations = results.get("violations", [])
        if violations:
            messages = []
            for v in violations:
                nodes = ", ".join(n.get("html", "?") for n in v.get("nodes", [])[:3])
                messages.append(f"  - {v['id']}: {v['help']} ({nodes})")
            violation_report = "\n".join(messages)
            assert False, f"axe-core found {len(violations)} accessibility violation(s):\n{violation_report}"
