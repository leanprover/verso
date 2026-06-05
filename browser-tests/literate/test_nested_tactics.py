from playwright.sync_api import Page


# `rw [h1, h2, h3]` in `LitConfig.lean` highlights as nested tactic regions: the whole-invocation
# region (own final state "All goals completed!") with one nested region per rewrite rule, each
# carrying that rule's intermediate proof state. Tactic regions nest now, so two things that used to
# be trivially true must be checked:
#   1. each region's hover shows that region's *own* state, not a nested descendant's (the original
#      bug showed the first rewrite step's state on the whole `rw`), and
#   2. hovering highlights only the most specific region under the pointer, even though `label:hover`
#      bubbles up to every enclosing region.
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

    def test_hover_highlights_most_specific_region(self, server: str, page: Page):
        """Hovering lights up only the most specific region containing the pointer; the enclosing
        regions, whose labels also receive `:hover`, stay unhighlighted."""
        self._load(server, page)
        rw = self._rw_keyword(page)
        rw.hover()

        # The highlight is a live CSS `:hover` effect (see the `:has(.tactic > label:hover)` rule in
        # `Highlighted.lean`). Hovering also spawns the proof-state tooltip and makes Firefox
        # recompute `:has(:hover)` on the next paint, so the background is not reliably settled on the
        # first read. Poll until the region's own label is highlighted before reading the rest. The
        # mouse stays put, so `:hover` persists across polls.
        handle = rw.element_handle()
        page.wait_for_function(
            """el => {
                const region = el.closest('.tactic');
                const bg = getComputedStyle(region.querySelector(':scope > label')).backgroundColor;
                return bg === 'rgb(238, 238, 238)';
            }""",
            arg=handle,
        )

        result = rw.evaluate(
            """el => {
                const bg = t => getComputedStyle(t.querySelector(':scope > label')).backgroundColor;
                const region = el.closest('.tactic');
                const ancestors = [];
                for (let a = region.parentElement.closest('.tactic'); a; a = a.parentElement.closest('.tactic')) {
                    ancestors.push(bg(a));
                }
                return { own: bg(region), ancestors };
            }"""
        )
        assert result["own"] == self.HIGHLIGHT
        # The example really is nested, so this assertion is meaningful.
        assert len(result["ancestors"]) > 0
        assert all(bg == self.TRANSPARENT for bg in result["ancestors"]), result[
            "ancestors"
        ]
