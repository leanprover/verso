"""End-to-end tests for the full-page search results view.

These tests exercise the Manual site built at `_out/html-multi`. Parallel suites live
under `browser-tests/literate/` and `browser-tests/verso-html/` for the other genres,
since they use different test projects.
"""

from playwright.sync_api import Page, expect


class TestSearchPage:
    def test_enter_navigates_to_search_page(self, server: str, page: Page):
        """Typing a query and pressing Enter (with no listbox selection) should land on
        `/search/?q=<query>`."""
        page.goto(f"{server}/")
        page.wait_for_load_state("networkidle")

        searchbox = page.get_by_role("searchbox")
        searchbox.focus()
        searchbox.type("Html", delay=20)
        searchbox.press("Escape")  # close dropdown so Enter isn't a select
        searchbox.press("Enter")

        page.wait_for_load_state("networkidle")
        assert "/search/" in page.url, f"expected to navigate to /search/, got {page.url}"
        assert "q=Html" in page.url, f"expected q=Html in URL, got {page.url}"

    def test_search_page_renders_results(self, server: str, page: Page):
        """Direct-loading `/search/?q=<query>` renders a list of results and the
        in-body search field is pre-filled with the query."""
        page.goto(f"{server}/search/?q=Html")
        page.wait_for_load_state("networkidle")

        # The input is a plain `<input type="search">` rendered by search-page.js.
        inbody_box = page.locator(".search-page-host .search-page-input")
        expect(inbody_box).to_be_visible()
        expect(inbody_box).to_have_value("Html")

        results = page.locator("ul.search-page-list li")
        expect(results.first).to_be_visible()
        assert results.count() >= 1

    def test_search_field_is_not_combobox(self, server: str, page: Page):
        """The in-body search field is a plain `<input type="search">`, not the
        quick-jump combobox: typing into it doesn't open a popup listbox."""
        page.goto(f"{server}/search/?q=Html")
        page.wait_for_load_state("networkidle")

        inbody_box = page.locator(".search-page-host .search-page-input")
        expect(inbody_box).to_be_visible()
        inbody_box.focus()
        inbody_box.press("ControlOrMeta+a")
        inbody_box.press("Delete")
        inbody_box.type("Verso", delay=30)

        # No dropdown/popup anywhere on the page.
        listbox = page.locator("[role='listbox']")
        assert listbox.count() == 0, "search page should not render a combobox listbox"
        # And specifically the combobox wrapper is absent.
        assert page.locator(".combobox-list").count() == 0

    def test_result_count_visible_at_top(self, server: str, page: Page):
        """The result count is always visible at the top of the results region."""
        page.goto(f"{server}/search/?q=Html")
        page.wait_for_load_state("networkidle")
        page.wait_for_function(
            "/\\d+ results?$/.test(document.getElementById('search-page-count')?.textContent ?? '')",
            timeout=5_000,
        )
        count = page.locator("#search-page-count")
        expect(count).to_be_visible()

    def test_result_count_updates_on_zero(self, server: str, page: Page):
        """On a gibberish query the count shows `0 results` rather than hiding."""
        page.goto(f"{server}/search/?q=xyzzyqwertasdf")
        page.wait_for_load_state("networkidle")
        page.wait_for_function(
            "document.getElementById('search-page-count')?.textContent === '0 results'",
            timeout=5_000,
        )

    def test_domain_filter_checkboxes_render(self, server: str, page: Page):
        """Filter row has one checkbox per domain plus a `Full-text` one, all checked
        by default."""
        page.goto(f"{server}/search/?q=Html")
        page.wait_for_load_state("networkidle")

        filters = page.locator(".search-page-filters")
        expect(filters).to_be_visible()

        boxes = page.locator(".search-page-filters input[type='checkbox']")
        # Some checkboxes; specifically a "Full-text" one is always present.
        assert boxes.count() >= 2, f"expected filter checkboxes, got {boxes.count()}"
        full_text = page.locator(".search-page-filter", has_text="Full-text")
        expect(full_text).to_be_visible()

        # All checked by default.
        checked = page.locator(".search-page-filters input[type='checkbox']:checked")
        assert checked.count() == boxes.count(), "all filters should be checked by default"

    def test_empty_bucket_filter_is_disabled(self, server: str, page: Page):
        """A query that yields hits in only some buckets should disable + gray the
        filters that have zero hits."""
        # Pick a query that's narrow enough that at least one domain has no matches.
        page.goto(f"{server}/search/?q=Html.visitM")
        page.wait_for_load_state("networkidle")
        page.wait_for_function(
            "/\\d+ (of \\d+ )?results?$/.test(document.getElementById('search-page-count')?.textContent ?? '')",
            timeout=5_000,
        )

        disabled = page.locator(".search-page-filter--disabled")
        assert disabled.count() >= 1, "expected at least one filter to be disabled for narrow query"
        # Any disabled label's checkbox should be disabled too.
        disabled_cbs = page.locator(".search-page-filter--disabled input[type='checkbox']:disabled")
        assert disabled_cbs.count() == disabled.count(), (
            "every .search-page-filter--disabled should have a :disabled checkbox"
        )

    def test_domain_filters_ordering(self, server: str, page: Page):
        """Full-text is first; the rest are alphabetized by display name."""
        page.goto(f"{server}/search/?q=Html")
        page.wait_for_load_state("networkidle")

        labels = page.locator(".search-page-filter").all_text_contents()
        labels = [t.strip() for t in labels]
        assert labels[0] == "Full-text", f"expected 'Full-text' first, got {labels[0]!r}"
        tail = labels[1:]
        assert tail == sorted(tail), f"domain filters not alphabetized: {tail}"

    def test_toggling_full_text_filter_changes_count(self, server: str, page: Page):
        """Unchecking the `Full-text` filter drops full-text-only results and the count
        decreases."""
        page.goto(f"{server}/search/?q=Html")
        page.wait_for_load_state("networkidle")
        page.wait_for_function(
            "/\\d+ results?$/.test(document.getElementById('search-page-count')?.textContent ?? '')",
            timeout=5_000,
        )

        before = page.locator("ul.search-page-list li").count()
        full_text_cb = page.locator(".search-page-filter", has_text="Full-text").locator("input")
        full_text_cb.uncheck()

        # After unchecking, count paragraph shows `M of N results` and results thin out.
        page.wait_for_function(
            "/of \\d+ results?$/.test(document.getElementById('search-page-count')?.textContent ?? '')",
            timeout=5_000,
        )
        after = page.locator("ul.search-page-list li").count()
        assert after < before, f"expected fewer results after unchecking full-text, {after} vs {before}"

    def test_full_text_header_em_is_inline(self, server: str, page: Page):
        """Matched characters inside a full-text result's `.header` should flow inline,
        not break the title across one line per matched character."""
        # Pick a multi-word query that's likely to produce a `<em>…</em>` per char
        # inside some full-text result's header.
        page.goto(f"{server}/search/?q=search")
        page.wait_for_load_state("networkidle")
        page.wait_for_function(
            "document.querySelector('ul.search-page-list li.search-result.full-text .header em') !== null",
            timeout=5_000,
        )
        display = page.locator("ul.search-page-list li.search-result.full-text .header em").first.evaluate(
            "el => getComputedStyle(el).display"
        )
        assert display in ("inline", "inline-block"), (
            f"em inside .header should flow inline, got display={display!r}"
        )

    def test_domain_css_applied_to_full_page_list(self, server: str, page: Page):
        """A per-domain CSS rule emitted into `domain-display.css` (e.g. bold structural
        font for `.section-domain`) should apply inside `.search-page-list`, not just
        inside the combobox dropdown."""
        page.goto(f"{server}/search/?q=Html")
        page.wait_for_load_state("networkidle")
        # Wait for the list to render.
        page.wait_for_function(
            "document.querySelector('ul.search-page-list .section-domain') !== null",
            timeout=5_000,
        )
        weight = page.locator("ul.search-page-list .section-domain").first.evaluate(
            "el => getComputedStyle(el).fontWeight"
        )
        # Bold is either "700" or "bold" depending on browser serialization.
        assert weight in ("700", "bold"), f"expected bold .section-domain, got {weight!r}"

    def test_site_title_still_shown_at_top(self, server: str, page: Page):
        """The site's book title is still rendered in the page header, and the page
        title `Search` is in the content."""
        page.goto(f"{server}/search/?q=Html")
        page.wait_for_load_state("networkidle")

        # Site title lives in the <header>; page heading lives in the main content.
        assert page.locator("header").count() > 0
        page_heading = page.locator("main h1, .search-page h1").first
        expect(page_heading).to_have_text("Search")

    def test_header_title_is_book_title_not_search(self, server: str, page: Page):
        """The `.header-title` should show the book title (not the literal word
        `Search`), matching the header on every other page."""
        # Load a non-search page to capture the canonical book title, then compare.
        page.goto(f"{server}/")
        page.wait_for_load_state("networkidle")
        expected = page.locator(".header-title h1").inner_text().strip()

        page.goto(f"{server}/search/?q=Html")
        page.wait_for_load_state("networkidle")
        actual = page.locator(".header-title h1").inner_text().strip()
        assert actual == expected, f"header-title changed on search page: {actual!r} vs {expected!r}"
        assert actual.lower() != "search", "header-title should be the book title, not 'Search'"

    def test_inbody_box_live_updates_results(self, server: str, page: Page):
        """Editing the in-body search field updates the results list without a page
        reload (the URL is kept in sync via history.replaceState)."""
        page.goto(f"{server}/search/?q=Html")
        page.wait_for_load_state("networkidle")

        inbody_box = page.locator(".search-page-host .search-page-input")
        expect(inbody_box).to_be_visible()
        initial_count = page.locator("ul.search-page-list li").count()
        assert initial_count >= 1

        # Stash a sentinel on window so we can detect a page reload.
        page.evaluate("window.__noReload = true")

        inbody_box.focus()
        inbody_box.press("ControlOrMeta+a")
        inbody_box.press("Delete")
        inbody_box.type("verso", delay=20)

        # Wait for debounce + re-render. The count paragraph ends with
        # `N result(s)` once the render completes.
        page.wait_for_function(
            "/\\d+ results?$/.test(document.getElementById('search-page-count')?.textContent ?? '')",
            timeout=5_000,
        )
        # The sentinel survives iff the page did NOT reload.
        assert page.evaluate("window.__noReload") is True, "page reloaded on input"
        # URL was updated in place.
        assert "q=verso" in page.url, f"expected q=verso, got {page.url}"

    def test_inbody_box_live_updates_on_character(self, server: str, page: Page):
        """Each keystroke extends the query and eventually updates the results."""
        page.goto(f"{server}/search/?q=H")
        page.wait_for_load_state("networkidle")

        inbody_box = page.locator(".search-page-host .search-page-input")
        expect(inbody_box).to_be_visible()
        page.evaluate("window.__noReload = true")

        inbody_box.focus()
        inbody_box.type("tml", delay=30)  # extends to "Html"

        # Eventually the URL reflects the final query.
        page.wait_for_function("new URL(location.href).searchParams.get('q') === 'Html'", timeout=5_000)
        assert page.evaluate("window.__noReload") is True, "page reloaded on input"

    def test_search_page_has_more_than_dropdown_cap(self, server: str, page: Page):
        """A broad query should yield more hits than the dropdown's 30-item cap. "lean"
        is a safe choice on this site: it's not on elasticlunr's stop-word list and
        appears frequently enough to exceed the cap."""
        page.goto(f"{server}/search/?q=lean")
        page.wait_for_load_state("networkidle")

        # Give search-page.js time to complete rendering (full-text results await
        # per-bucket loads).
        page.wait_for_function(
            "document.querySelectorAll('ul.search-page-list li').length > 30",
            timeout=15_000,
        )
        results = page.locator("ul.search-page-list li")
        assert results.count() > 30, f"expected >30 results, got {results.count()}"

    def test_empty_query_shows_placeholder(self, server: str, page: Page):
        """With no `q` parameter the count region shows a prompt to type."""
        page.goto(f"{server}/search/")
        page.wait_for_load_state("networkidle")

        count = page.locator("#search-page-count")
        expect(count).to_be_visible()
        expect(count).to_have_text("Type a query in the search box to see results.")

    def test_click_result_navigates(self, server: str, page: Page):
        """Clicking a result should navigate away from the search page."""
        page.goto(f"{server}/search/?q=Html")
        page.wait_for_load_state("networkidle")

        first_result = page.locator("ul.search-page-list li").first
        expect(first_result).to_be_visible()
        first_result.click()
        page.wait_for_load_state("networkidle")

        assert "/search/" not in page.url, f"expected navigation away from /search/, got {page.url}"

    def test_enter_with_listbox_selection_still_jumps(self, server: str, page: Page):
        """Regression: Enter with a selected listbox item still navigates to that item,
        not to the search page."""
        page.goto(f"{server}/")
        page.wait_for_load_state("networkidle")

        searchbox = page.get_by_role("searchbox")
        searchbox.focus()
        searchbox.type("Html.visitM", delay=20)
        # Arrow down to focus the listbox, then Enter → jumps to the selected item.
        searchbox.press("ArrowDown")
        searchbox.press("Enter")
        page.wait_for_load_state("networkidle")

        assert "/search/" not in page.url, f"Enter with selection should not go to /search/, got {page.url}"
