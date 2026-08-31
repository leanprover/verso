"""Tests for margin-note numbering in the Manual genre.

These tests run against the built package-manual example site: build it with
``lake exe packagedocs --output _out/package-manual`` and pass
``--site-dir _out/package-manual/html-multi``.

Margin notes (also used for bibliography citations) are numbered by the CSS
counter ``margin-note-counter``: each note increments it, a superscript mark
after the note's anchor shows the number in the text, and the note itself
repeats it in the margin. Successive notes on a page must show successive
numbers.

Rendered counter values live only in the layout tree, out of reach of script
in both engines: the computed ``content`` of a pseudo-element keeps
``counter()`` unresolved, and generated text is absent from the accessibility
tree. The test therefore reads the numbering through geometry: the note floats
out of the ``.marginalia`` span, leaving the superscript mark as the span's
only in-flow content, and the fixture page (the "Notes" section of the
package-manual document) has enough notes that a correctly advancing counter
reaches two digits, making the later marks wider than the first.
"""

from pathlib import Path

import pytest
from playwright.sync_api import Page

# The fixture page has at least this many margin notes, so its tenth mark shows
# a two-digit number.
NUM_NOTES = 10


@pytest.fixture(scope="session")
def notes_page_path(request) -> str:
    """URL path of the page with the margin-note numbering fixture, located by
    scanning the built site for the page with the most margin notes."""
    site_dir = Path(__file__).parent.parent / request.config.getoption("--site-dir")
    best, best_count = None, 0
    for html_file in site_dir.rglob("*.html"):
        count = html_file.read_text(errors="ignore").count('class="marginalia"')
        if count > best_count:
            best, best_count = html_file, count
    assert best is not None and best_count >= NUM_NOTES, (
        f"Expected a page with at least {NUM_NOTES} margin notes in {site_dir}"
    )
    return "/" + best.relative_to(site_dir).as_posix().removesuffix("index.html")


def mark_widths(page: Page) -> list[float]:
    """Width of each note's superscript number mark. The ``.note`` floats out of
    the ``.marginalia`` span, so the span's own box holds just the
    ``.marginalia::after`` mark showing the counter value."""
    return page.eval_on_selector_all(
        ".marginalia",
        "els => els.map(el => el.getBoundingClientRect().width)",
    )


class TestMarginNoteNumbering:
    def test_successive_notes_get_successive_numbers(
        self, server: str, page: Page, notes_page_path: str
    ):
        page.goto(f"{server}{notes_page_path}")
        page.wait_for_load_state("networkidle")

        widths = mark_widths(page)
        assert len(widths) >= NUM_NOTES
        for w in widths:
            assert w > 0, "Expected every note to render a visible number mark"

        # Notes 1 through 9 have one-digit marks of equal width; note 10 has a
        # wider two-digit mark. If the counter never advances, every note shows
        # "1" and all marks are equally wide.
        assert widths[9] > widths[0] + 2, (
            f"Expected note 10 to show a two-digit number, but its mark is the "
            f"same width as note 1's ({widths}): the margin-note counter is not "
            f"advancing, so every note shows the number 1"
        )
        assert max(widths[:9]) - min(widths[:9]) < 0.5, (
            f"Expected notes 1 through 9 to show one-digit numbers ({widths})"
        )
