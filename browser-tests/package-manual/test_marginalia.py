"""Test Manual marginalia in browsers.

Build the package-manual example with
``lake exe packagedocs --output _out/package-manual`` and run these tests with
``--site-dir _out/package-manual/html-multi``.
"""

from pathlib import Path

import pytest
from playwright.sync_api import Browser, Page


NUM_NOTES = 10


@pytest.fixture(scope="session")
def notes_page_path(request) -> str:
    """Return the generated page containing the marginalia stress fixture."""
    site_dir = Path(__file__).parent.parent / request.config.getoption("--site-dir")
    best, best_count = None, 0
    for html_file in site_dir.rglob("*.html"):
        contents = html_file.read_text(errors="ignore")
        count = contents.count('class="marginalia-note"')
        if count > best_count:
            best, best_count = html_file, count
    assert best is not None and best_count >= NUM_NOTES, (
        f"Expected a page with at least {NUM_NOTES} margin notes in {site_dir}"
    )
    return "/" + best.relative_to(site_dir).as_posix().removesuffix("index.html")


def goto_notes(page: Page, server: str, notes_page_path: str) -> None:
    page.goto(f"{server}{notes_page_path}")
    page.wait_for_load_state("networkidle")


class TestDesktopMarginalia:
    def test_markers_and_bodies_are_visible_and_numbered(
        self, server: str, page: Page, notes_page_path: str
    ):
        page.set_viewport_size({"width": 1600, "height": 900})
        goto_notes(page, server, notes_page_path)

        references = page.locator(".marginalia-reference")
        notes = page.locator(".marginalia-note")
        assert references.count() >= NUM_NOTES
        assert notes.count() == references.count()
        assert notes.first.is_visible()
        assert page.locator(".marginalia-marker-desktop").first.is_visible()
        assert not page.locator(".marginalia-marker-mobile").first.is_visible()

        widths = references.evaluate_all(
            "els => els.map(el => el.getBoundingClientRect().width)"
        )
        assert all(width > 0 for width in widths)
        assert widths[9] > widths[0] + 2
        assert max(widths[:9]) - min(widths[:9]) < 0.5

    def test_notes_clear_one_another(
        self, server: str, page: Page, notes_page_path: str
    ):
        page.set_viewport_size({"width": 1600, "height": 900})
        goto_notes(page, server, notes_page_path)
        boxes = page.locator(".marginalia-note").evaluate_all(
            "els => els.map(el => el.getBoundingClientRect().toJSON())"
        )
        for previous, current in zip(boxes, boxes[1:]):
            assert current["top"] >= previous["bottom"] - 0.5

        bottom_gap = page.locator(".content-wrapper").evaluate(
            """wrapper => {
                const notes = [...wrapper.querySelectorAll('.marginalia-note')];
                const bottom = Math.max(...notes.map(
                    note => note.getBoundingClientRect().bottom
                ));
                return wrapper.getBoundingClientRect().bottom - bottom;
            }"""
        )
        assert bottom_gap >= 16

    def test_marker_and_note_share_hover_highlight(
        self, server: str, page: Page, notes_page_path: str
    ):
        page.set_viewport_size({"width": 1600, "height": 900})
        goto_notes(page, server, notes_page_path)

        reference = page.locator(".marginalia-reference").first
        marker = reference.locator("[aria-details]")
        note = page.locator(f"#{marker.get_attribute('aria-details')}")
        original = note.evaluate("el => getComputedStyle(el).backgroundColor")

        reference.hover()
        assert reference.evaluate("el => el.classList.contains('marginalia-highlight')")
        assert note.evaluate("el => el.classList.contains('marginalia-highlight')")
        highlighted = note.evaluate("el => getComputedStyle(el).backgroundColor")
        assert highlighted != original
        assert reference.evaluate("el => getComputedStyle(el).backgroundColor") == highlighted

        note.hover()
        assert reference.evaluate("el => el.classList.contains('marginalia-highlight')")
        assert note.evaluate("el => el.classList.contains('marginalia-highlight')")
        assert reference.evaluate("el => getComputedStyle(el).backgroundColor") == highlighted

    def test_hoisted_marker_and_note_share_hover_highlight(
        self, server: str, page: Page, notes_page_path: str
    ):
        page.set_viewport_size({"width": 1600, "height": 900})
        goto_notes(page, server, notes_page_path)

        note = page.locator(".marginalia-note", has_text="Hoisted table note one")
        note_id = note.get_attribute("id")
        reference = page.locator(
            f'.marginalia-reference:has([aria-details="{note_id}"])'
        )
        original = note.evaluate("el => getComputedStyle(el).backgroundColor")

        reference.hover()
        assert reference.evaluate("el => el.classList.contains('marginalia-highlight')")
        assert note.evaluate("el => el.classList.contains('marginalia-highlight')")
        highlighted = note.evaluate("el => getComputedStyle(el).backgroundColor")
        assert highlighted != original
        assert reference.evaluate("el => getComputedStyle(el).backgroundColor") == highlighted

        note.hover()
        assert reference.evaluate("el => el.classList.contains('marginalia-highlight')")
        assert note.evaluate("el => el.classList.contains('marginalia-highlight')")
        assert reference.evaluate("el => getComputedStyle(el).backgroundColor") == highlighted

    def test_table_notes_are_hoisted_in_source_order(
        self, server: str, page: Page, notes_page_path: str
    ):
        page.set_viewport_size({"width": 1600, "height": 900})
        goto_notes(page, server, notes_page_path)

        first = page.locator(".marginalia-note", has_text="Hoisted table note one")
        second = page.locator(".marginalia-note", has_text="Hoisted table note two")
        assert first.count() == second.count() == 1
        assert page.locator("table .marginalia-reference").count() >= 2
        assert first.evaluate("el => el.previousElementSibling.tagName") == "TABLE"
        assert second.evaluate("el => el.previousElementSibling.tagName") == "TABLE"
        assert first.evaluate(
            "(a, b) => Boolean(a.compareDocumentPosition(b) & Node.DOCUMENT_POSITION_FOLLOWING)",
            second.element_handle(),
        )
        typography = """el => {
            const style = getComputedStyle(el);
            return {
                fontFamily: style.fontFamily,
                fontSize: style.fontSize,
                fontWeight: style.fontWeight,
                fontStyle: style.fontStyle,
                lineHeight: style.lineHeight,
                color: style.color,
                textAlign: style.textAlign,
                whiteSpace: style.whiteSpace,
            };
        }"""
        ordinary_typography = page.locator(
            ".marginalia-note", has_text="Note two"
        ).evaluate(typography)
        assert first.evaluate(typography) == ordinary_typography

    def test_docstring_note_is_hoisted_after_its_box(
        self, server: str, page: Page, notes_page_path: str
    ):
        page.set_viewport_size({"width": 1600, "height": 900})
        goto_notes(page, server, notes_page_path)

        note = page.locator(".marginalia-note", has_text="Hoisted docstring note")
        assert note.count() == 1
        box = page.locator(".namedocs", has=page.locator(".marginalia-reference"))
        assert box.count() == 1
        assert box.locator(".marginalia-note").count() == 0
        assert note.evaluate("el => el.previousElementSibling.classList.contains('namedocs')")

    def test_rewrite_annotations_do_not_reach_serialized_html(
        self, request, notes_page_path: str
    ):
        site_dir = Path(__file__).parent.parent / request.config.getoption("--site-dir")
        html_file = site_dir / (notes_page_path.removeprefix("/") + "index.html")
        contents = html_file.read_text()
        for attribute in (
            "data-verso-hoist",
            "data-verso-barrier",
            "data-verso-no-barrier",
            "data-verso-suppress",
            "data-verso-suppressible",
        ):
            assert attribute not in contents


class TestMobileMarginalia:
    def test_native_popover_interaction(
        self, server: str, page: Page, notes_page_path: str
    ):
        page.set_viewport_size({"width": 390, "height": 800})
        goto_notes(page, server, notes_page_path)

        marker = page.locator(".marginalia-marker-mobile").first
        note_id = marker.get_attribute("popovertarget")
        note = page.locator(f"#{note_id}")

        assert marker.is_visible()
        assert marker.get_by_text("Show marginal note").count() == 1
        assert note.get_attribute("role") == "note"
        assert not note.is_visible()

        marker.click()
        assert note.evaluate("el => el.matches(':popover-open')")
        assert note.is_visible()
        center_offset = note.evaluate(
            """el => {
                const box = el.getBoundingClientRect();
                return {
                    x: Math.abs(box.left + box.width / 2 - innerWidth / 2),
                    y: Math.abs(box.top + box.height / 2 - innerHeight / 2),
                };
            }"""
        )
        assert center_offset["x"] <= 1
        assert center_offset["y"] <= 1

        page.keyboard.press("Escape")
        assert not note.evaluate("el => el.matches(':popover-open')")

        marker.click()
        page.locator("h1").click(position={"x": 2, "y": 2})
        assert not note.evaluate("el => el.matches(':popover-open')")

    def test_entering_desktop_closes_an_open_popover(
        self, server: str, page: Page, notes_page_path: str
    ):
        page.set_viewport_size({"width": 390, "height": 800})
        goto_notes(page, server, notes_page_path)
        marker = page.locator(".marginalia-marker-mobile").first
        note = page.locator(f"#{marker.get_attribute('popovertarget')}")

        marker.click()
        assert note.evaluate("el => el.matches(':popover-open')")
        page.set_viewport_size({"width": 1200, "height": 800})

        assert not note.evaluate("el => el.matches(':popover-open')")
        assert note.is_visible()
        assert page.locator(".marginalia-marker-desktop").first.is_visible()

    def test_native_interaction_works_without_javascript(
        self, browser: Browser, server: str, notes_page_path: str
    ):
        context = browser.new_context(
            java_script_enabled=False,
            viewport={"width": 390, "height": 800},
        )
        page = context.new_page()
        try:
            goto_notes(page, server, notes_page_path)
            marker = page.locator(".marginalia-marker-mobile").first
            note = page.locator(f"#{marker.get_attribute('popovertarget')}")
            assert marker.is_visible()
            assert not note.is_visible()
            marker.click()
            assert note.is_visible()
        finally:
            context.close()
