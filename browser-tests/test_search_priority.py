"""Unit tests for the pure priority-combining helpers exported from search-box.js.

These drive the real in-browser code path without touching search UI state: each test loads the
served site (which already pulls in `search-box.js` as a module), then `page.evaluate`s a dynamic
`import()` and calls the named exports with crafted inputs. This catches regressions in the
combining math (e.g. multiplicative stacking creeping back in, a lost layer in the sum, a neutral
value drifting) that wire-format tests on the Lean side can't see.
"""

import math

from playwright.sync_api import Page


# Relative to the site root served by conftest's fixture.
SEARCH_BOX_PATH = "/-verso-search/search-box.js"


class TestPriorityContribution:
    def test_neutral_and_undefined(self, server: str, page: Page):
        """50, undefined, and null all yield the neutral contribution 0."""
        page.goto(server)
        result = page.evaluate(
            f"""async () => {{
                const m = await import('{SEARCH_BOX_PATH}');
                return {{
                    fifty: m.priorityContribution(50),
                    undef: m.priorityContribution(undefined),
                    nul: m.priorityContribution(null),
                }};
            }}"""
        )
        assert result["fifty"] == 0
        assert result["undef"] == 0
        assert result["nul"] == 0

    def test_symmetric_around_neutral(self, server: str, page: Page):
        """+k and -k are inverses in the log-space scheme: their contributions sum to zero."""
        page.goto(server)
        result = page.evaluate(
            f"""async () => {{
                const m = await import('{SEARCH_BOX_PATH}');
                return [
                    m.priorityContribution(75) + m.priorityContribution(25),
                    m.priorityContribution(60) + m.priorityContribution(40),
                    m.priorityContribution(99) + m.priorityContribution(1),
                ];
            }}"""
        )
        for pair_sum in result:
            assert abs(pair_sum) < 1e-12

    def test_edges_of_0_99_range(self, server: str, page: Page):
        """0 → -1 (halving), 99 → +0.98 (near doubling)."""
        page.goto(server)
        result = page.evaluate(
            f"""async () => {{
                const m = await import('{SEARCH_BOX_PATH}');
                return {{
                    zero: m.priorityContribution(0),
                    ninetyNine: m.priorityContribution(99),
                }};
            }}"""
        )
        assert result["zero"] == -1.0
        assert result["ninetyNine"] == (99 - 50) / 50


class TestCombineScore:
    def test_all_neutral_layers_preserve_score(self, server: str, page: Page):
        """A raw score with neutral (or absent) priorities is returned unchanged."""
        page.goto(server)
        result = page.evaluate(
            f"""async () => {{
                const m = await import('{SEARCH_BOX_PATH}');
                return [
                    m.combineScore(0.42),
                    m.combineScore(0.42, 50, 50, 50),
                    m.combineScore(0.42, undefined, undefined),
                    m.combineScore(0.42, null, 50, undefined),
                ];
            }}"""
        )
        for score in result:
            assert abs(score - 0.42) < 1e-12

    def test_layers_compose_additively_not_multiplicatively(
        self, server: str, page: Page
    ):
        """Three layers at 75 contribute +0.5 each, stacking to 2^1.5 ≈ 2.828, not 1.5^3 = 3.375.

        This is the load-bearing property that justifies the log-space scheme.
        """
        page.goto(server)
        result = page.evaluate(
            f"""async () => {{
                const m = await import('{SEARCH_BOX_PATH}');
                return m.combineScore(1, 75, 75, 75);
            }}"""
        )
        assert abs(result - (2**1.5)) < 1e-12
        # And crucially: NOT the multiplicative outcome.
        assert abs(result - 3.375) > 0.5

    def test_opposing_layers_cancel(self, server: str, page: Page):
        """Boost + suppress of equal magnitude returns to neutral."""
        page.goto(server)
        result = page.evaluate(
            f"""async () => {{
                const m = await import('{SEARCH_BOX_PATH}');
                return [
                    m.combineScore(1, 75, 25),
                    m.combineScore(1, 90, 10),
                    m.combineScore(1, 75, 75, 25, 25),
                ];
            }}"""
        )
        for score in result:
            assert abs(score - 1) < 1e-12

    def test_single_layer_matches_expected_multipliers(self, server: str, page: Page):
        """Exercise specific multipliers that appear in documentation: 75 → √2, 25 → 1/√2, 0 → 1/2."""
        page.goto(server)
        result = page.evaluate(
            f"""async () => {{
                const m = await import('{SEARCH_BOX_PATH}');
                return {{
                    boost: m.combineScore(1, 75),
                    deemphasize: m.combineScore(1, 25),
                    half: m.combineScore(1, 0),
                }};
            }}"""
        )
        assert abs(result["boost"] - math.sqrt(2)) < 1e-12
        assert abs(result["deemphasize"] - 1 / math.sqrt(2)) < 1e-12
        assert abs(result["half"] - 0.5) < 1e-12

    def test_out_of_range_priorities_behave_linearly(self, server: str, page: Page):
        """Pre-summed ancestor contributions may drift outside [0, 99]; the formula extends.

        A value of 150 means a +100 deviation, i.e. +2 in log space → 4×.
        """
        page.goto(server)
        result = page.evaluate(
            f"""async () => {{
                const m = await import('{SEARCH_BOX_PATH}');
                return [
                    m.combineScore(1, 150),   // +2 exponent
                    m.combineScore(1, -50),   // -2 exponent
                ];
            }}"""
        )
        assert abs(result[0] - 4.0) < 1e-12
        assert abs(result[1] - 0.25) < 1e-12
