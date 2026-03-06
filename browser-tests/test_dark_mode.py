from playwright.sync_api import Browser, Page, expect


def get_theme_state(page: Page) -> tuple[str | None, str | None]:
    html_theme = page.evaluate("() => document.documentElement.getAttribute('data-theme')")
    stored_theme = page.evaluate("() => localStorage.getItem('verso-theme')")
    return html_theme, stored_theme

def get_color_scheme(page: Page) -> str:
    return page.evaluate("""() => getComputedStyle(document.documentElement).colorScheme""")


def get_body_background(page: Page) -> str:
    return page.evaluate("""() => getComputedStyle(document.body).backgroundColor""")


def select_theme(page: Page, theme: str) -> None:
    page.locator("#theme-toggle-button").click()
    page.locator(f'#theme-toggle-menu [data-theme-option="{theme}"]').click()


class TestDarkMode:
    def test_theme_toggle_asset_is_present_and_served(self, server: str, page: Page):
        page.goto(f"{server}/Verso-Markup")

        script = page.locator('script[src="theme-toggle.js"]')
        expect(script).to_have_count(1)

        response = page.request.get(f"{server}/theme-toggle.js")
        assert response.ok
        assert response.status == 200

    def test_theme_menu_updates_storage(self, server: str, page: Page):
        page.emulate_media(color_scheme="light")
        page.goto(f"{server}/Verso-Markup")

        toggle = page.locator("#theme-toggle-button")
        expect(toggle).to_have_count(1)

        initial_theme, initial_stored = get_theme_state(page)
        assert initial_theme is None
        assert initial_stored is None
        assert get_color_scheme(page) == "light"

        select_theme(page, "dark")
        first_theme, first_stored = get_theme_state(page)
        assert first_theme == "dark"
        assert first_stored == "dark"
        assert get_color_scheme(page) == "dark"

        select_theme(page, "light")
        second_theme, second_stored = get_theme_state(page)
        assert second_theme == "light"
        assert second_stored == "light"
        assert get_color_scheme(page) == "light"

        select_theme(page, "system")
        third_theme, third_stored = get_theme_state(page)
        assert third_theme is None
        assert third_stored is None
        assert get_color_scheme(page) == "light"

    def test_theme_preference_persists_across_page_loads(self, server: str, browser: Browser):
        context = browser.new_context(color_scheme="light")
        try:
            first_page = context.new_page()
            first_page.goto(f"{server}/Verso-Markup")
            select_theme(first_page, "dark")

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

    def test_dark_system_preference_can_be_overridden_to_light(self, server: str, page: Page):
        page.emulate_media(color_scheme="dark")
        page.goto(f"{server}/Verso-Markup")

        initial_theme, initial_stored = get_theme_state(page)
        assert initial_theme is None
        assert initial_stored is None
        assert get_body_background(page) == "rgb(30, 30, 30)"
        assert get_color_scheme(page) == "dark"

        select_theme(page, "light")
        first_theme, first_stored = get_theme_state(page)
        assert first_theme == "light"
        assert first_stored == "light"
        assert get_body_background(page) == "rgb(255, 255, 255)"
        assert get_color_scheme(page) == "light"

        select_theme(page, "system")
        second_theme, second_stored = get_theme_state(page)
        assert second_theme is None
        assert second_stored is None
        assert get_body_background(page) == "rgb(30, 30, 30)"
        assert get_color_scheme(page) == "dark"

    def test_dark_mode_styles_require_opt_in_attribute(self, server: str, page: Page):
        page.emulate_media(color_scheme="dark")
        page.goto(f"{server}/Verso-Markup")

        attr = page.evaluate("() => document.documentElement.hasAttribute('data-verso-dark-mode')")
        assert attr is True
        assert get_body_background(page) == "rgb(30, 30, 30)"
        assert get_color_scheme(page) == "dark"

        page.evaluate("() => document.documentElement.removeAttribute('data-verso-dark-mode')")
        assert get_body_background(page) == "rgb(255, 255, 255)"
        assert get_color_scheme(page) == "light"

        page.evaluate("() => document.documentElement.setAttribute('data-verso-dark-mode', 'true')")
        assert get_body_background(page) == "rgb(30, 30, 30)"
        assert get_color_scheme(page) == "dark"

    def test_dark_mode_still_applies_without_javascript(self, server: str, browser: Browser):
        context = browser.new_context(color_scheme="dark", java_script_enabled=False)
        try:
            page = context.new_page()
            page.goto(f"{server}/Verso-Markup")

            assert get_body_background(page) == "rgb(30, 30, 30)"
            assert get_color_scheme(page) == "dark"
            expect(page.locator("#theme-toggle")).to_be_hidden()
        finally:
            context.close()
