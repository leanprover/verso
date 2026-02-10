from playwright.sync_api import Browser, Page, expect


def get_theme_state(page: Page) -> tuple[str | None, str | None]:
    html_theme = page.evaluate("() => document.documentElement.getAttribute('data-theme')")
    stored_theme = page.evaluate("() => localStorage.getItem('verso-theme')")
    return html_theme, stored_theme


def get_css_var(page: Page, variable_name: str) -> str:
    return page.evaluate(
        """([name]) => getComputedStyle(document.documentElement).getPropertyValue(name).trim()""",
        [variable_name],
    )


class TestDarkMode:
    def test_theme_toggle_asset_is_present_and_served(self, server: str, page: Page):
        page.goto(f"{server}/Verso-Markup")

        script = page.locator('script[src="theme-toggle.js"]')
        expect(script).to_have_count(1)

        response = page.request.get(f"{server}/theme-toggle.js")
        assert response.ok
        assert response.status == 200

    def test_theme_toggle_cycles_and_updates_storage(self, server: str, page: Page):
        page.emulate_media(color_scheme="light")
        page.goto(f"{server}/Verso-Markup")

        toggle = page.locator("#theme-toggle")
        expect(toggle).to_have_count(1)

        initial_theme, initial_stored = get_theme_state(page)
        assert initial_theme is None
        assert initial_stored is None

        toggle.click()
        first_theme, first_stored = get_theme_state(page)
        assert first_theme == "dark"
        assert first_stored == "dark"

        toggle.click()
        second_theme, second_stored = get_theme_state(page)
        assert second_theme == "light"
        assert second_stored == "light"

        toggle.click()
        third_theme, third_stored = get_theme_state(page)
        assert third_theme is None
        assert third_stored is None

    def test_theme_preference_persists_across_page_loads(self, server: str, browser: Browser):
        context = browser.new_context(color_scheme="light")
        try:
            first_page = context.new_page()
            first_page.goto(f"{server}/Verso-Markup")
            first_page.locator("#theme-toggle").click()

            first_theme, first_stored = get_theme_state(first_page)
            assert first_theme == "dark"
            assert first_stored == "dark"

            second_page = context.new_page()
            second_page.goto(f"{server}/Verso-Markup")

            second_theme, second_stored = get_theme_state(second_page)
            assert second_theme == "dark"
            assert second_stored == "dark"
        finally:
            context.close()

    def test_dark_mode_styles_require_opt_in_attribute(self, server: str, page: Page):
        page.emulate_media(color_scheme="dark")
        page.goto(f"{server}/Verso-Markup")

        attr = page.evaluate("() => document.documentElement.hasAttribute('data-verso-dark-mode')")
        assert attr is True
        assert get_css_var(page, "--verso-background-color") == "#1e1e1e"

        page.evaluate("() => document.documentElement.removeAttribute('data-verso-dark-mode')")
        assert get_css_var(page, "--verso-background-color") == "#ffffff"

        page.evaluate("() => document.documentElement.setAttribute('data-verso-dark-mode', 'true')")
        assert get_css_var(page, "--verso-background-color") == "#1e1e1e"
