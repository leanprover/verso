from playwright.sync_api import Page, expect


def toc_width(page: Page) -> float:
    return page.locator("#toc").evaluate(
        "el => el.getBoundingClientRect().width"
    )


class TestTocResize:
    def test_pointer_resize_updates_width_and_persists(self, server: str, page: Page):
        """Dragging the ToC resize handle changes the ToC width and stores it."""
        page.set_viewport_size({"width": 1200, "height": 800})
        page.goto(f"{server}/")
        page.wait_for_load_state("networkidle")

        handle = page.locator(".toc-resize-handle")
        expect(handle).to_be_visible()

        initial = toc_width(page)
        box = handle.bounding_box()
        assert box is not None, "Expected visible ToC resize handle"

        page.mouse.move(box["x"] + box["width"] / 2, box["y"] + 20)
        page.mouse.down()
        page.mouse.move(box["x"] + box["width"] / 2 + 96, box["y"] + 20)
        page.mouse.up()

        resized = toc_width(page)
        assert resized > initial + 80, (
            f"Expected drag to widen ToC from {initial}px, got {resized}px"
        )

        stored = page.evaluate("localStorage.getItem('verso-toc-width')")
        assert stored is not None
        assert abs(float(stored) - resized) <= 1

        page.reload()
        page.wait_for_load_state("networkidle")
        persisted = toc_width(page)
        assert abs(persisted - resized) <= 1, (
            f"Expected persisted ToC width {resized}px after reload, got {persisted}px"
        )

    def test_resize_handle_accessibility_and_keyboard(self, server: str, page: Page):
        """The initialized resize handle is keyboard-operable and exposes ARIA state."""
        page.set_viewport_size({"width": 1200, "height": 800})
        page.goto(f"{server}/")
        page.wait_for_load_state("networkidle")

        handle = page.get_by_role("separator", name="Resize table of contents")
        expect(handle).to_be_visible()
        expect(handle).to_have_attribute("aria-orientation", "vertical")
        expect(handle).to_have_attribute("tabindex", "0")
        expect(handle).to_have_attribute("aria-valuemin", "160")

        initial = toc_width(page)
        initial_value = handle.get_attribute("aria-valuenow")
        assert initial_value is not None
        assert abs(float(initial_value) - round(initial)) <= 1

        handle.focus()
        expect(handle).to_be_focused()
        page.keyboard.press("ArrowRight")

        widened = toc_width(page)
        assert widened > initial, (
            f"Expected ArrowRight to widen ToC from {initial}px, got {widened}px"
        )
        widened_value = handle.get_attribute("aria-valuenow")
        assert widened_value is not None
        assert abs(float(widened_value) - round(widened)) <= 1

        page.keyboard.press("Home")
        min_width = toc_width(page)
        assert abs(min_width - 160) <= 1, (
            f"Expected Home to set ToC to minimum width, got {min_width}px"
        )
        expect(handle).to_have_attribute("aria-valuenow", "160")

    def test_resize_handle_is_inert_without_javascript(self, server: str, browser):
        """Without JS, the handle is present but does not advertise an active control."""
        context = browser.new_context(java_script_enabled=False)
        page = context.new_page()
        try:
            page.set_viewport_size({"width": 1200, "height": 800})
            page.goto(f"{server}/")
            page.wait_for_load_state("domcontentloaded")

            handle = page.locator(".toc-resize-handle")
            expect(handle).to_be_visible()
            expect(handle).not_to_have_attribute("role", "separator")
            expect(handle).not_to_have_attribute("tabindex", "0")

            cursor = handle.evaluate("el => getComputedStyle(el).cursor")
            assert cursor != "col-resize", (
                f"Expected no resize cursor without JS, got {cursor}"
            )
        finally:
            context.close()

    def test_saved_desktop_width_is_ignored_on_mobile(self, server: str, page: Page):
        """Mobile keeps the CSS default ToC width even when a desktop width is saved."""
        page.set_viewport_size({"width": 1200, "height": 800})
        page.goto(f"{server}/")
        page.wait_for_load_state("networkidle")
        page.evaluate("localStorage.setItem('verso-toc-width', '640')")

        page.set_viewport_size({"width": 390, "height": 800})
        page.reload()
        page.wait_for_load_state("networkidle")

        width = toc_width(page)
        assert abs(width - 288) <= 1, (
            f"Expected mobile ToC to keep the 18rem CSS default width, got {width}px"
        )
        inline_width = page.evaluate(
            "document.documentElement.style.getPropertyValue('--verso-toc-width')"
        )
        assert inline_width == "", (
            f"Expected no inline ToC width on mobile, got {inline_width!r}"
        )
