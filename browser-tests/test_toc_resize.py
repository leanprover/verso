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
        # The saved width is recorded as a custom property; the
        # stylesheet, not the script, is what ignores it on mobile.
        user_width = page.evaluate(
            "document.documentElement.style.getPropertyValue('--verso-toc-user-width')"
        )
        assert user_width == "640px", (
            f"Expected the saved width to remain as a custom property, got {user_width!r}"
        )

    def test_saved_width_applies_when_widening_from_mobile(self, server: str, page: Page):
        """Growing past the mobile breakpoint applies the saved width without a reload."""
        page.set_viewport_size({"width": 1200, "height": 800})
        page.goto(f"{server}/")
        page.wait_for_load_state("networkidle")
        page.evaluate("localStorage.setItem('verso-toc-width', '420')")

        # Load narrow, then widen in place. The stylesheet swaps to the saved width.
        page.set_viewport_size({"width": 390, "height": 800})
        page.reload()
        page.wait_for_load_state("networkidle")
        assert abs(toc_width(page) - 288) <= 1

        page.set_viewport_size({"width": 1200, "height": 800})
        widened = toc_width(page)
        assert abs(widened - 420) <= 1, (
            f"Expected the saved 420px width on desktop, got {widened}px"
        )

    def test_resize_reflows_content_layout_live(self, server: str, page: Page):
        """Resizing the ToC re-evaluates main-width container queries without a reload.

        The content centering and margin-note layout are driven by ``@container``
        queries on ``<main>``, whose width tracks the ToC width. This is a regression
        test for a Firefox-specific bug: when ``<main>`` reserved space for the ToC with
        ``padding`` (driven by an inherited custom property), Firefox did not
        re-evaluate the container queries on the live size change, so the layout only
        updated after a reload. Reserving the space with ``margin`` keeps ``<main>``'s
        border-box width tied to the ToC width, which every engine re-queries on. This
        test only catches the regression when run under Firefox; the conftest runs it
        under both engines.
        """
        # A wide viewport so the content column starts centered with the default ToC.
        page.set_viewport_size({"width": 1600, "height": 900})
        page.goto(f"{server}/")
        page.wait_for_load_state("networkidle")
        page.evaluate("localStorage.removeItem('verso-toc-width')")
        page.reload()
        page.wait_for_load_state("networkidle")

        def content_max_width() -> str:
            # The centered regime gives .content-wrapper a max-width; the left-aligned
            # regime does not. So max-width is a clean signal for which @container rule
            # is currently applied.
            return page.locator(".content-wrapper").first.evaluate(
                "el => getComputedStyle(el).maxWidth"
            )

        assert content_max_width() != "none", (
            "Expected the content to start centered at a wide viewport with the default ToC"
        )

        # Drag the ToC wide enough to shrink the main content area below the centering
        # threshold, without reloading.
        handle = page.locator(".toc-resize-handle")
        box = handle.bounding_box()
        assert box is not None, "Expected a visible ToC resize handle"
        page.mouse.move(box["x"] + box["width"] / 2, box["y"] + 200)
        page.mouse.down()
        page.mouse.move(box["x"] + box["width"] / 2 + 500, box["y"] + 200)
        page.mouse.up()

        assert content_max_width() == "none", (
            "Expected the content to stop centering once the widened ToC shrinks the "
            "main content area, without a reload (the container query must re-evaluate "
            "live)"
        )
