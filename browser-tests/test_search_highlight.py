"""Tests for search-term highlighting on pages reached from full-text search results, and for the
highlighted snippets in the results themselves."""

import re

from playwright.sync_api import Page, expect

# A page with many occurrences of "paragraph", "paragraphs", and "Paragraphs".
PAGE = "Verso-Markup/"
TERM = "paragraph"
HIGHLIGHTS = "main section span.text-search-results"


def section_text(page: Page) -> str:
    """Returns the text of the sections that are searched for terms."""
    return page.evaluate(
        "() => Array.from(document.querySelectorAll('main section'), s => s.textContent).join('\\n')"
    )


def open_page(server: str, page: Page, terms: str | None) -> list[str]:
    """Opens the test page, optionally with search terms, and returns the page errors."""
    errors: list[str] = []
    page.on("pageerror", lambda e: errors.append(str(e)))
    query = "" if terms is None else f"?terms={terms}"
    page.goto(f"{server}/{PAGE}{query}")
    page.wait_for_load_state("networkidle")
    return errors


def add_paragraph(page: Page, html: str) -> None:
    """Adds content to the first searched section and highlights the page again."""
    page.evaluate(
        """(html) => {
            removeHighlights();
            document.querySelector('main section').insertAdjacentHTML('beforeend', html);
            highlightSearchTerms();
        }""",
        html,
    )


class TestPageHighlights:
    def test_matches_are_wrapped(self, server: str, page: Page):
        errors = open_page(server, page, TERM)
        highlights = page.locator(HIGHLIGHTS)
        assert highlights.count() >= 3
        texts = highlights.all_text_contents()
        assert all(t.lower().startswith(TERM) for t in texts), texts
        # Stemming matches inflected forms too.
        assert {"paragraph", "paragraphs"} <= {t.lower() for t in texts}
        titles = set(highlights.evaluate_all("els => els.map(e => e.title)"))
        assert titles == {f"Result for “{TERM}”"}
        assert errors == []

    def test_prefix_matches(self, server: str, page: Page):
        errors = open_page(server, page, "para")
        texts = page.locator(HIGHLIGHTS).all_text_contents()
        assert texts and all(t.lower().startswith("para") for t in texts), texts
        assert any(t.lower().startswith(TERM) for t in texts)
        assert errors == []

    def test_text_is_unchanged(self, server: str, page: Page):
        open_page(server, page, None)
        original = section_text(page)
        errors = open_page(server, page, TERM)
        assert page.locator(HIGHLIGHTS).count() > 0
        assert section_text(page) == original
        assert errors == []

    def test_several_matches_in_one_text_node(self, server: str, page: Page):
        errors = open_page(server, page, TERM)
        add_paragraph(
            page,
            '<p id="hl-test">One paragraph, then two paragraphs, then the end.</p>',
        )
        added = page.locator("#hl-test")
        expect(added).to_have_text("One paragraph, then two paragraphs, then the end.")
        expect(added.locator("span.text-search-results")).to_have_text(
            ["paragraph", "paragraphs"]
        )
        assert added.evaluate("p => p.childNodes.length") == 5
        assert errors == []

    def test_no_matches_leaves_text_alone(self, server: str, page: Page):
        errors = open_page(server, page, TERM)
        add_paragraph(page, '<p id="hl-test">Nothing to see here.</p>')
        added = page.locator("#hl-test")
        expect(added).to_have_text("Nothing to see here.")
        assert added.evaluate("p => p.childNodes.length") == 1
        assert errors == []

    def test_navigation(self, server: str, page: Page):
        errors = open_page(server, page, TERM)
        total = page.locator(HIGHLIGHTS).count()
        count = page.locator("#highlight-count")
        expect(count).to_have_text(f"0/{total}")

        page.locator("#highlight-next").click()
        expect(count).to_have_text(f"1/{total}")
        expect(page.locator(HIGHLIGHTS).nth(0)).to_have_class(
            re.compile(r"\bfocused\b")
        )
        expect(page.locator("#highlight-current")).to_have_text(
            page.locator(HIGHLIGHTS).nth(0).text_content() or ""
        )

        page.locator("#highlight-next").click()
        expect(count).to_have_text(f"2/{total}")
        expect(page.locator(HIGHLIGHTS).nth(1)).to_have_class(
            re.compile(r"\bfocused\b")
        )
        expect(page.locator(f"{HIGHLIGHTS}.focused")).to_have_count(1)

        page.locator("#highlight-prev").click()
        expect(count).to_have_text(f"1/{total}")
        page.locator("#highlight-prev").click()
        expect(count).to_have_text(f"{total}/{total}")
        assert errors == []

    def test_clicking_a_highlight_selects_it(self, server: str, page: Page):
        errors = open_page(server, page, TERM)
        total = page.locator(HIGHLIGHTS).count()
        page.locator(HIGHLIGHTS).nth(2).click()
        expect(page.locator("#highlight-count")).to_have_text(f"3/{total}")
        assert errors == []

    def test_match_in_closed_details_is_opened(self, server: str, page: Page):
        errors = open_page(server, page, TERM)
        add_paragraph(
            page,
            '<details id="hl-details"><summary>More</summary><p>A hidden paragraph.</p></details>',
        )
        index = page.evaluate(
            "() => allHighlights.findIndex(h => h.closest('#hl-details') !== null)"
        )
        assert index >= 0
        assert (
            page.evaluate("() => document.getElementById('hl-details').open") is False
        )
        page.evaluate("(i) => scrollToHighlight(i)", index)
        assert page.evaluate("() => document.getElementById('hl-details').open") is True
        assert errors == []

    def test_close_restores_text(self, server: str, page: Page):
        open_page(server, page, None)
        original = section_text(page)
        errors = open_page(server, page, TERM)
        page.locator("#highlight-close").click()
        expect(page.locator(HIGHLIGHTS)).to_have_count(0)
        expect(page.locator("#highlight-controls")).to_have_count(0)
        assert section_text(page) == original
        assert errors == []

    def test_no_terms_no_highlights(self, server: str, page: Page):
        errors = open_page(server, page, None)
        expect(page.locator(HIGHLIGHTS)).to_have_count(0)
        expect(page.locator("#highlight-controls")).to_have_count(0)
        assert errors == []


class TestResultSnippets:
    def test_full_text_snippets(self, server: str, page: Page):
        errors: list[str] = []
        page.on("pageerror", lambda e: errors.append(str(e)))
        page.goto(f"{server}/search/?q={TERM}")
        results = page.locator("ul.search-page-list li.search-result.full-text")
        expect(results.first).to_be_visible(timeout=5_000)

        snippets = results.locator("p > span:not(.header)")
        assert snippets.count() > 0
        for i in range(min(snippets.count(), 5)):
            snippet = snippets.nth(i)
            emphasized = snippet.locator("em").all_text_contents()
            assert emphasized, snippet.inner_html()
            assert all(t.lower().startswith(TERM) for t in emphasized), emphasized
            text = snippet.text_content() or ""
            # The snippets are plain text with the matches emphasized.
            assert "<em>" not in text and "</em>" not in text, text
            # Each match appears in the snippet's text where it is emphasized.
            for t in emphasized:
                assert t in text
        assert errors == []
