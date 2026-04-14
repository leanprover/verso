from playwright.sync_api import expect, Page


# The CSS selector used by the tooltip initialization code
TIPPY_SELECTOR = (
    ".hl.lean .const.token, .hl.lean .keyword.token, .hl.lean .literal.token, "
    ".hl.lean .option.token, .hl.lean .var.token, .hl.lean .typed.token, "
    ".hl.lean .has-info, .hl.lean .tactic, .hl.lean .level-var, "
    ".hl.lean .level-const, .hl.lean .level-op, .hl.lean .sort"
)


class TestTooltips:
    """Tests for Tippy tooltip behavior on code elements."""

    def test_tippy_instances_on_load(self, server: str, page: Page):
        """Tippy instances should be eagerly created on page load."""
        page.goto(f"{server}/LitConfig/Core/")
        page.wait_for_load_state("networkidle")

        # There should be tooltip-eligible elements on the page
        count = page.locator(".hl.lean .const.token").count()
        assert count > 0, "Expected .const.token elements on the page"

        # All eligible elements should have Tippy instances after load
        tippy_count = page.evaluate(
            f"() => document.querySelectorAll('{TIPPY_SELECTOR}').length"
        )
        initialized = page.evaluate(
            f"""() => {{
            const els = document.querySelectorAll('{TIPPY_SELECTOR}');
            return Array.from(els).filter(el => el._tippy).length;
        }}"""
        )
        assert tippy_count > 0, "Expected tooltip-eligible elements"
        assert initialized == tippy_count, (
            f"Expected all {tippy_count} elements to have Tippy instances, "
            f"but only {initialized} were initialized"
        )

    def test_hover_creates_tooltip(self, server: str, page: Page):
        """Hovering a code token should show a Tippy tooltip."""
        page.goto(f"{server}/LitConfig/Core/")
        page.wait_for_load_state("networkidle")

        token = page.locator(".hl.lean .const.token").first
        expect(token).to_be_visible()

        # Hover the token
        token.hover()

        # Wait for the Tippy instance to be created (it uses showOnCreate)
        page.wait_for_function(
            "el => !!el._tippy",
            arg=token.element_handle(),
            timeout=5000,
        )

        # The tippy-box should be visible in the DOM
        tippy_box = page.locator(".tippy-box")
        expect(tippy_box.first).to_be_visible()

    def test_tooltip_has_correct_theme(self, server: str, page: Page):
        """Tooltip theme should match the element type."""
        page.goto(f"{server}/LitConfig/Core/")
        page.wait_for_load_state("networkidle")

        token = page.locator(".hl.lean .const.token").first
        expect(token).to_be_visible()

        token.hover()
        page.wait_for_function(
            "el => !!el._tippy",
            arg=token.element_handle(),
            timeout=5000,
        )

        theme = token.get_attribute("data-tippy-theme")
        assert theme == "lean", f"Expected theme 'lean' for .const.token, got '{theme}'"

    def test_repeat_hover_reuses_instance(self, server: str, page: Page):
        """Hovering the same token twice should reuse the cached Tippy instance."""
        page.goto(f"{server}/LitConfig/Core/")
        page.wait_for_load_state("networkidle")

        token = page.locator(".hl.lean .const.token").first
        expect(token).to_be_visible()

        # First hover
        token.hover()
        page.wait_for_function(
            "el => !!el._tippy",
            arg=token.element_handle(),
            timeout=5000,
        )

        # Record the instance id
        first_id = page.evaluate("el => el._tippy.id", token.element_handle())

        # Move away, then hover again
        page.mouse.move(0, 0)
        page.wait_for_timeout(200)
        token.hover()
        page.wait_for_timeout(200)

        # Should be the same instance
        second_id = page.evaluate("el => el._tippy.id", token.element_handle())
        assert first_id == second_id, (
            f"Expected same Tippy instance on re-hover (id {first_id}), got new instance (id {second_id})"
        )
