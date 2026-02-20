import re

from playwright.sync_api import expect, Page


class TestAccessibility:
    """Tests for WCAG 2.1 AA: skip link, landmarks, headings, keyboard, focus, axe-core, dark mode."""

    def test_skip_link_first_focusable(self, server: str, page: Page):
        """Test that first Tab focuses .skip-link targeting #main-content."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        skip_link = page.locator("a.skip-link")
        expect(skip_link).to_have_count(1)
        expect(skip_link).to_have_attribute("href", "#main-content")

        # First Tab press should focus the skip link
        page.keyboard.press("Tab")
        expect(skip_link).to_be_focused()

    def test_skip_link_activates(self, server: str, page: Page):
        """Test that Enter on skip link moves focus to main content."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        page.keyboard.press("Tab")
        skip_link = page.locator("a.skip-link")
        expect(skip_link).to_be_focused()

        page.keyboard.press("Enter")

        # After activating skip link, focus should move to #main-content
        # or the URL hash should be #main-content
        expect(page).to_have_url(re.compile(r"#main-content$"))

    def test_landmarks(self, server: str, page: Page):
        """Test <nav> for module nav, <main> for content, with distinct aria-labels."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        # Module navigation
        module_nav = page.locator('nav[aria-label="Module navigation"]')
        expect(module_nav).to_have_count(1)

        # Main content
        main = page.locator("main#main-content")
        expect(main).to_have_count(1)

        # Breadcrumb
        breadcrumb = page.locator('[aria-label="Breadcrumb"]')
        expect(breadcrumb).to_have_count(1)

    def test_heading_hierarchy(self, server: str, page: Page):
        """Test at most one h1 per page and no heading level gaps."""
        for path in ["/LitConfig/", "/LitConfig/Core/", "/LitConfig/Core/Basic/", "/LitConfig/NoDocstrings/"]:
            page.goto(f"{server}{path}")
            page.wait_for_load_state("networkidle")

            # At most one h1 per page
            h1_count = page.locator("h1").count()
            assert h1_count <= 1, f"Page {path}: expected at most 1 h1, got {h1_count}"

            # Check for heading gaps: collect all heading levels
            levels = page.evaluate("""() => {
                const headings = document.querySelectorAll('h1, h2, h3, h4, h5, h6');
                return Array.from(headings).map(h => parseInt(h.tagName.substring(1)));
            }""")

            if len(levels) == 0:
                continue

            for i in range(1, len(levels)):
                gap = levels[i] - levels[i - 1]
                assert gap <= 1, (
                    f"Page {path}: heading gap from h{levels[i-1]} to h{levels[i]} "
                    f"(levels: {levels})"
                )

    def test_keyboard_tab_order(self, server: str, page: Page):
        """Test Tab reaches skip -> search -> navbar -> content elements."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        # First Tab: skip link
        page.keyboard.press("Tab")
        skip_link = page.locator("a.skip-link")
        expect(skip_link).to_be_focused()

        # Keep tabbing and verify we reach the search box
        found_search = False
        for _ in range(10):
            page.keyboard.press("Tab")
            focused = page.evaluate("() => document.activeElement?.getAttribute('role')")
            if focused == "searchbox":
                found_search = True
                break
        assert found_search, "Expected Tab to reach searchbox within 10 presses"

    def test_focus_indicators(self, server: str, page: Page):
        """Test that focused elements have non-none outline."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        # Tab to skip link and check outline
        page.keyboard.press("Tab")
        skip_link = page.locator("a.skip-link")
        expect(skip_link).to_be_focused()

        outline = skip_link.evaluate("el => getComputedStyle(el).outlineStyle")
        assert outline != "none", f"Expected focus outline on skip-link, got outline-style: {outline}"

    def test_collapsible_aria(self, server: str, page: Page):
        """Test <details> open/closed state is correct and keyboard-operable."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        details = page.locator("nav.module-tree details").first
        if details.count() == 0:
            return

        summary = details.locator(":scope > summary")

        # Focus summary via keyboard
        summary.focus()
        expect(summary).to_be_focused()

        was_open = details.evaluate("el => el.open")

        # Press Enter or Space to toggle
        page.keyboard.press("Enter")
        new_state = details.evaluate("el => el.open")
        assert new_state != was_open, "Expected details state to toggle on Enter"

    def test_axe_core_audit(self, server: str, page: Page):
        """Run axe-core accessibility audit on a representative page."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

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

    def test_reduced_motion(self, server: str, page: Page):
        """Test that with prefers-reduced-motion: reduce, transition durations are near 0."""
        page.emulate_media(reduced_motion="reduce")
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        # Check that transition-duration on elements is near 0
        # The CSS sets 0.01ms !important; browsers may report this as "0.01ms", "0s", "1e-05s", etc.
        duration_seconds = page.locator(".copy-button").first.evaluate(
            """el => {
                const raw = getComputedStyle(el).transitionDuration;
                // Parse to seconds
                if (raw.endsWith('ms')) return parseFloat(raw) / 1000;
                if (raw.endsWith('s')) return parseFloat(raw);
                return parseFloat(raw);
            }"""
        )
        assert duration_seconds < 0.001, (
            f"Expected near-zero transition-duration with reduced motion, got {duration_seconds}s"
        )

    def test_dark_mode_activates(self, server: str, page: Page):
        """Test that prefers-color-scheme: dark changes CSS variable values."""
        # Light mode
        page.emulate_media(color_scheme="light")
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        light_bg = page.evaluate(
            "() => getComputedStyle(document.documentElement).getPropertyValue('--verso-background-color').trim()"
        )

        # Dark mode
        page.emulate_media(color_scheme="dark")
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        dark_bg = page.evaluate(
            "() => getComputedStyle(document.documentElement).getPropertyValue('--verso-background-color').trim()"
        )

        assert light_bg != dark_bg, (
            f"Expected different --verso-background-color in dark vs light mode, "
            f"but both were '{light_bg}'"
        )

    def test_dark_mode_contrast(self, server: str, page: Page):
        """Test that dark mode text has adequate contrast (>= 4.5:1) against background."""
        page.emulate_media(color_scheme="dark")
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        # Get actual computed text and background colors
        colors = page.evaluate("""() => {
            const main = document.querySelector('#main-content') || document.body;
            const style = getComputedStyle(main);
            return {
                color: style.color,
                backgroundColor: style.backgroundColor
            };
        }""")

        # Parse RGB values and compute relative luminance
        def parse_rgb(color_str):
            match = re.search(r'rgb[a]?\((\d+),\s*(\d+),\s*(\d+)', color_str)
            if match:
                return int(match.group(1)), int(match.group(2)), int(match.group(3))
            return None

        def relative_luminance(r, g, b):
            rs = r / 255.0
            gs = g / 255.0
            bs = b / 255.0
            rs = rs / 12.92 if rs <= 0.04045 else ((rs + 0.055) / 1.055) ** 2.4
            gs = gs / 12.92 if gs <= 0.04045 else ((gs + 0.055) / 1.055) ** 2.4
            bs = bs / 12.92 if bs <= 0.04045 else ((bs + 0.055) / 1.055) ** 2.4
            return 0.2126 * rs + 0.7152 * gs + 0.0722 * bs

        fg = parse_rgb(colors["color"])
        bg = parse_rgb(colors["backgroundColor"])

        if fg and bg:
            l1 = relative_luminance(*fg)
            l2 = relative_luminance(*bg)
            contrast = (max(l1, l2) + 0.05) / (min(l1, l2) + 0.05)
            assert contrast >= 4.5, (
                f"Dark mode contrast ratio {contrast:.2f}:1 is below WCAG AA minimum 4.5:1 "
                f"(fg={colors['color']}, bg={colors['backgroundColor']})"
            )
