"""Test Manual marginalia in browsers.

Build the package-manual example with
``lake exe packagedocs --output _out/package-manual`` and run these tests with
``--site-dir _out/package-manual/html-multi``.
"""

import re
from pathlib import Path

import pytest
from playwright.sync_api import Browser, Locator, Page


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


@pytest.fixture(scope="session")
def table_stress_page_path(request) -> str:
    """Return the page containing only the table marginalia stress fixture."""
    site_dir = Path(__file__).parent.parent / request.config.getoption("--site-dir")
    matches = []
    for html_file in site_dir.rglob("*.html"):
        if "Stress table row ten" in html_file.read_text(errors="ignore"):
            matches.append(html_file)
    assert len(matches) == 1
    return "/" + matches[0].relative_to(site_dir).as_posix().removesuffix("index.html")


def goto_notes(page: Page, server: str, notes_page_path: str) -> None:
    page.goto(f"{server}{notes_page_path}")
    page.wait_for_load_state("networkidle")


def note_with_text(page: Page, text: str) -> Locator:
    """Return the margin note whose entire text is ``text``."""
    return page.locator(".marginalia-note").filter(
        has_text=re.compile(rf"^\s*{re.escape(text)}\s*$")
    )


def hover(page: Page, element: Locator) -> None:
    """Move the pointer onto ``element``.

    Playwright's own hover aims at the element's content boxes, which leave out CSS generated
    content. A reference marker's visible content is its ``::after`` counter, so that aim
    lands on the surrounding paragraph. The bounding rect includes generated content.
    """
    center = element.evaluate(
        """el => {
            el.scrollIntoView({block: "center"});
            const box = el.getBoundingClientRect();
            return {x: box.left + box.width / 2, y: box.top + box.height / 2};
        }"""
    )
    page.mouse.move(center["x"], center["y"])


def wait_for_popover_closed(note: Locator) -> None:
    note.page.wait_for_function(
        "el => !el.matches(':popover-open')", arg=note.element_handle()
    )


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

    def test_note_numbers_render_beside_their_notes(
        self, server: str, page: Page, notes_page_path: str
    ):
        page.set_viewport_size({"width": 1600, "height": 900})
        goto_notes(page, server, notes_page_path)

        # The number is a ::before box positioned beside the note. A point inside that box
        # hit-tests to the note only while the box is drawn, so a note that clips its own
        # overflow hides the number and hit-tests to the page behind it instead.
        numbered = page.locator(".marginalia-note").evaluate_all(
            """els => els.map(el => {
                el.scrollIntoView({block: "center"});
                const box = el.getBoundingClientRect();
                const note = getComputedStyle(el);
                const number = getComputedStyle(el, "::before");
                const x = box.left + parseFloat(number.left) + parseFloat(number.width) / 2;
                const y = box.top + parseFloat(note.paddingTop) + parseFloat(note.lineHeight) / 2;
                return document.elementFromPoint(x, y) === el;
            })"""
        )
        assert len(numbered) >= NUM_NOTES
        assert all(numbered)

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
        marker = reference.locator("[aria-details]").first
        note = page.locator(f"#{marker.get_attribute('aria-details')}")
        original = note.evaluate("el => getComputedStyle(el).backgroundColor")

        hover(page, reference)
        assert reference.evaluate("el => el.classList.contains('marginalia-highlight')")
        assert note.evaluate("el => el.classList.contains('marginalia-highlight')")
        highlighted = note.evaluate("el => getComputedStyle(el).backgroundColor")
        assert highlighted != original
        assert (
            reference.evaluate("el => getComputedStyle(el).backgroundColor")
            == highlighted
        )

        hover(page, note)
        assert reference.evaluate("el => el.classList.contains('marginalia-highlight')")
        assert note.evaluate("el => el.classList.contains('marginalia-highlight')")
        assert (
            reference.evaluate("el => getComputedStyle(el).backgroundColor")
            == highlighted
        )

    def test_hoisted_marker_and_note_share_hover_highlight(
        self, server: str, page: Page, notes_page_path: str
    ):
        page.set_viewport_size({"width": 1600, "height": 900})
        goto_notes(page, server, notes_page_path)

        note = note_with_text(page, "Hoisted table note one")
        note_id = note.get_attribute("id")
        reference = page.locator(
            f'.marginalia-reference:has([aria-details="{note_id}"])'
        )
        original = note.evaluate("el => getComputedStyle(el).backgroundColor")

        hover(page, reference)
        assert reference.evaluate("el => el.classList.contains('marginalia-highlight')")
        assert note.evaluate("el => el.classList.contains('marginalia-highlight')")
        highlighted = note.evaluate("el => getComputedStyle(el).backgroundColor")
        assert highlighted != original
        assert (
            reference.evaluate("el => getComputedStyle(el).backgroundColor")
            == highlighted
        )

        hover(page, note)
        assert reference.evaluate("el => el.classList.contains('marginalia-highlight')")
        assert note.evaluate("el => el.classList.contains('marginalia-highlight')")
        assert (
            reference.evaluate("el => getComputedStyle(el).backgroundColor")
            == highlighted
        )

    def test_table_notes_are_hoisted_in_source_order(
        self, server: str, page: Page, notes_page_path: str
    ):
        page.set_viewport_size({"width": 1600, "height": 900})
        goto_notes(page, server, notes_page_path)

        first = note_with_text(page, "Hoisted table note one")
        second = note_with_text(page, "Hoisted table note two")
        assert first.count() == second.count() == 1
        assert page.locator("table .marginalia-reference").count() >= 2
        first_table = first.locator("xpath=following-sibling::*[1]")
        second_table = second.locator("xpath=following-sibling::*[1]")
        assert first_table.evaluate("el => el.tagName") == "TABLE"
        assert second_table.evaluate("el => el.tagName") == "TABLE"
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
        ordinary_typography = note_with_text(page, "Note two").evaluate(typography)
        assert first.evaluate(typography) == ordinary_typography

    def test_last_row_notes_extend_the_page_without_overlapping(
        self, server: str, page: Page, table_stress_page_path: str
    ):
        page.set_viewport_size({"width": 1600, "height": 900})
        goto_notes(page, server, table_stress_page_path)

        table = page.locator("table.tabular", has_text="Stress table row one")
        notes = page.locator(
            ".marginalia-note",
            has_text="Stress table note",
        )
        assert page.locator("table.tabular").count() == 1
        assert table.locator("tr").count() == 10
        assert table.locator("tr").last.locator(".marginalia-reference").count() == 8
        assert table.locator(".marginalia-note").count() == 0
        assert notes.count() == 8
        assert notes.last.locator("xpath=following-sibling::*[1]").evaluate(
            "(el, table) => el === table", table.element_handle()
        )

        table_box = table.bounding_box()
        note_boxes = notes.evaluate_all(
            "els => els.map(el => el.getBoundingClientRect().toJSON())"
        )
        assert table_box is not None
        assert abs(note_boxes[0]["top"] - table_box["y"]) <= 1
        for previous, current in zip(note_boxes, note_boxes[1:]):
            assert current["top"] >= previous["bottom"] - 0.5
        assert note_boxes[-1]["bottom"] > table_box["y"] + table_box["height"]

        wrapper_bottom = page.locator(".content-wrapper").evaluate(
            "el => el.getBoundingClientRect().bottom"
        )
        assert wrapper_bottom - note_boxes[-1]["bottom"] >= 16
        document_bottom = page.evaluate("document.documentElement.scrollHeight")
        assert document_bottom - note_boxes[-1]["bottom"] >= 16

    def test_docstring_note_is_hoisted_before_its_box(
        self, server: str, page: Page, notes_page_path: str
    ):
        page.set_viewport_size({"width": 1600, "height": 900})
        goto_notes(page, server, notes_page_path)

        note = note_with_text(page, "Hoisted docstring note")
        assert note.count() == 1
        box = page.locator(".namedocs", has=page.locator(".marginalia-reference"))
        assert box.count() == 1
        assert box.locator(".marginalia-note").count() == 0
        assert note.locator("xpath=following-sibling::*[1]").evaluate(
            "(el, box) => el === box", box.element_handle()
        )
        assert note.evaluate("el => getComputedStyle(el).marginTop") == "0px"

    def test_markers_reference_their_note_details(
        self, server: str, page: Page, notes_page_path: str
    ):
        page.set_viewport_size({"width": 1600, "height": 900})
        goto_notes(page, server, notes_page_path)

        for marker_class in (
            ".marginalia-marker-desktop",
            ".marginalia-marker-mobile",
        ):
            markers = page.locator(marker_class)
            described = markers.evaluate_all(
                "els => els.map(el => el.getAttribute('aria-details'))"
            )
            assert all(note_id for note_id in described)
            assert all(
                page.locator(f"#{note_id}").count() == 1 for note_id in described
            )

    def test_nav_buttons_omit_marginalia_from_titles(
        self, server: str, page: Page, notes_page_path: str, table_stress_page_path: str
    ):
        page.set_viewport_size({"width": 1600, "height": 900})
        goto_notes(page, server, table_stress_page_path)
        heading = page.locator("main h1").first
        assert heading.locator(".marginalia-reference").count() == 1

        goto_notes(page, server, notes_page_path)
        next_button = page.locator(".prev-next-buttons a[rel=next]").first
        assert (
            next_button.locator(".where").inner_text() == "4. Table Marginalia Stress"
        )
        assert next_button.get_attribute("title") == "4. Table Marginalia Stress"

        next_button.click()
        page.wait_for_load_state("networkidle")
        next_button = page.locator(".prev-next-buttons a[rel=next]").first
        next_button.click()
        page.wait_for_load_state("networkidle")
        prev_button = page.locator(".prev-next-buttons a[rel=prev]").first
        assert (
            prev_button.locator(".where").inner_text() == "4. Table Marginalia Stress"
        )
        assert prev_button.get_attribute("title") == "4. Table Marginalia Stress"

    def test_rewrite_annotations_do_not_reach_serialized_html(
        self, request, notes_page_path: str
    ):
        site_dir = Path(__file__).parent.parent / request.config.getoption("--site-dir")
        html_file = site_dir / (notes_page_path.removeprefix("/") + "index.html")
        contents = html_file.read_text()
        for attribute in (
            "data-verso-hoist",
            "data-verso-barrier",
            "data-verso-barrier-before",
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
        wait_for_popover_closed(note)

        marker.click()
        page.locator("main h1").first.click(position={"x": 2, "y": 2})
        wait_for_popover_closed(note)

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

        wait_for_popover_closed(note)
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
