from playwright.sync_api import Page

from hover_media import require_hover_media


# `rw [h1, h2, h3]` in `LitConfig.lean` highlights as nested tactic regions: the whole-invocation
# region (own final state "All goals completed!") with one nested region per rewrite rule, each
# carrying that rule's intermediate proof state. Tactic regions nest now, so two things that used to
# be trivially true must be checked:
#   1. each region's hover shows that region's *own* state, not a nested descendant's (the original
#      bug showed the first rewrite step's state on the whole `rw`), and
#   2. hovering highlights only the innermost region under the pointer, even though `label:hover`
#      bubbles up to every enclosing region. A collapsed region's proof state is the tooltip for
#      everything in its label, documented tokens included, so the label is what highlights.
class TestNestedTacticStates:
    """Hover behavior for nested tactic regions (multi-step `rw`)."""

    URL_PATH = "/LitConfig/"

    HIGHLIGHT = "rgb(238, 238, 238)"  # #eeeeee, the label-hover background
    TRANSPARENT = "rgba(0, 0, 0, 0)"

    def _load(self, server: str, page: Page):
        page.goto(f"{server}{self.URL_PATH}")
        page.wait_for_load_state("networkidle")

    def _rw_keyword(self, page: Page):
        # The `rw` keyword is direct content of the whole-`rw` region, not of any rule region.
        return page.locator('.hl.lean .keyword.token[data-binding*="rwSeq"]').first

    @staticmethod
    def _region_tooltip_text(token):
        """Text that the hover tooltip shows for the tactic region enclosing `token`. Reads the
        region's own Tippy instance, which runs the same `content()` callback as a real hover but
        avoids the race where several overlapping regions' tooltips are briefly visible at once."""
        return token.evaluate(
            """el => {
                const inst = el.closest('.tactic')._tippy;
                inst.show();
                const text = inst.popper.querySelector('.tippy-content').innerText;
                inst.hide();
                return text;
            }"""
        )

    def test_region_owns_its_state_in_the_dom(self, server: str, page: Page):
        """A region's own state is its *direct-child* `.tactic-state` (what the hover reads). For the
        whole `rw` it is the final state, which differs from the first rewrite step nested inside."""
        self._load(server, page)
        own, first_descendant = self._rw_keyword(page).evaluate(
            """el => {
                const region = el.closest('.tactic');
                return [
                    region.querySelector(':scope > .tactic-state').innerText,
                    region.querySelector('.tactic-state').innerText,
                ];
            }"""
        )
        assert "All goals completed" in own
        # The first *descendant* state is the first rewrite step's intermediate goal. Reading it for
        # the whole `rw` (a plain descendant query) was the original bug, so the two must differ.
        assert "All goals completed" not in first_descendant
        assert "Nat" in first_descendant  # it is a real goal, with hypotheses

    def test_hover_whole_rw_shows_final_state(self, server: str, page: Page):
        """The whole-`rw` region's tooltip shows its own final state."""
        self._load(server, page)
        text = self._region_tooltip_text(self._rw_keyword(page))
        assert "All goals completed" in text
        # Regression guard: not the first rewrite step's intermediate goal (which lists hypotheses).
        assert "Nat" not in text

    def test_hover_rewrite_step_shows_its_own_state(self, server: str, page: Page):
        """A single rewrite rule's tooltip shows that rule's intermediate goal, not the enclosing
        `rw`'s final state."""
        self._load(server, page)
        # The first variable after the `rw` keyword is `h1`, inside its own rule region.
        step = self._rw_keyword(page).locator(
            "xpath=following::span[contains(@class,'var') and contains(@class,'token')][1]"
        )
        text = self._region_tooltip_text(step)
        assert "All goals completed" not in text
        assert "Nat" in text  # a real intermediate goal

    @staticmethod
    def _region_label_backgrounds(tok):
        """Backgrounds of the labels of every tactic region enclosing `tok`, innermost first."""
        return tok.evaluate(
            """el => {
                const bg = t => getComputedStyle(t.querySelector(':scope > label')).backgroundColor;
                const regions = [];
                for (let a = el.closest('.tactic'); a; a = a.parentElement.closest('.tactic')) {
                    regions.push(bg(a));
                }
                return regions;
            }"""
        )

    def test_hover_highlights_own_region_label(self, server: str, page: Page):
        """Hovering a region's plain content highlights that region's label."""
        self._load(server, page)
        require_hover_media(page)
        # The `rw` keyword is direct content of the whole-`rw` region.
        tok = self._rw_keyword(page)
        tok.hover()
        # The highlight is a live CSS `:hover` effect that Firefox settles on the next paint,
        # so poll until it lands. The mouse stays put, so `:hover` persists across polls.
        page.wait_for_function(
            """el => getComputedStyle(el.closest('.tactic').querySelector(':scope > label'))
                .backgroundColor === 'rgb(238, 238, 238)'""",
            arg=tok.element_handle(),
        )

    def test_hover_highlights_most_specific_region(self, server: str, page: Page):
        """Hovering lights up only the innermost tactic region's label, even for a documented
        token: the region's proof state is the tooltip shown there, so the token itself stays
        plain and enclosing regions' labels stay unhighlighted."""
        self._load(server, page)
        require_hover_media(page)
        # The first rewrite rule (`h1`, a documented token) is nested inside its own step region,
        # which is nested inside the whole-`rw` region.
        tok = self._rw_keyword(page).locator(
            "xpath=following::span[contains(@class,'var') and contains(@class,'token')][1]"
        )
        tok.hover()

        # The highlight is a live CSS `:hover` effect. Hovering also spawns a tooltip and makes
        # Firefox recompute `:has(:hover)` on the next paint, so the background is not reliably
        # settled on the first read. Poll until the step label is highlighted before reading the
        # rest. The mouse stays put, so `:hover` persists across polls.
        handle = tok.element_handle()
        page.wait_for_function(
            """el => getComputedStyle(el.closest('.tactic').querySelector(':scope > label'))
                .backgroundColor === 'rgb(238, 238, 238)'""",
            arg=handle,
        )

        regions = self._region_label_backgrounds(tok)
        assert (
            tok.evaluate("el => getComputedStyle(el).backgroundColor")
            == self.TRANSPARENT
        )
        # The example really is nested, so the outer-region assertion is meaningful.
        assert len(regions) > 1
        assert regions[0] == self.HIGHLIGHT
        assert all(bg == self.TRANSPARENT for bg in regions[1:]), regions

    def test_collapsed_step_owns_tooltip_inside_expanded_region(
        self, server: str, page: Page
    ):
        """Expanding the whole-`rw` region attaches tippy instances to the content of the step
        regions nested inside it, which stay collapsed. Hovering a documented token in a
        collapsed step still shows that step's proof state, tippy instance notwithstanding."""
        self._load(server, page)
        # Expand the whole-`rw` region; the step regions inside stay collapsed.
        self._rw_keyword(page).evaluate(
            "el => el.closest('.tactic').querySelector(':scope > input.tactic-toggle').click()"
        )
        tok = self._rw_keyword(page).locator(
            "xpath=following::span[contains(@class,'var') and contains(@class,'token')][1]"
        )
        assert tok.evaluate("el => !!el._tippy"), (
            "expansion should attach a tippy to the token"
        )
        tok.hover()
        box = page.locator(".tippy-box[data-theme~='tactic']").first
        box.wait_for(state="visible")
        # The step's own intermediate goal, not the whole `rw`'s final state.
        assert "All goals completed" not in box.inner_text()
        assert "Nat" in box.inner_text()
