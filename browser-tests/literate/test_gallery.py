"""Tests for the code rendering gallery page (LitConfig.Gallery).

The gallery module contains at least one instance of every kind of code rendering, so
these tests check that each one is present in the generated page and that hovering
produces the right tooltip theme.
"""

from playwright.sync_api import Page

from hover_media import require_hover_media


GALLERY = "/LitConfig/Gallery/"


class TestGalleryContents:
    def test_all_renderings_present(self, server: str, page: Page):
        page.goto(f"{server}{GALLERY}")
        page.wait_for_load_state("networkidle")
        counts = page.evaluate(
            """() => ({
                warning: document.querySelectorAll('.hl.lean .has-info.warning').length,
                information: document.querySelectorAll('.hl.lean .has-info.information').length,
                tactics: document.querySelectorAll('.hl.lean .tactic').length,
                tacticStates: document.querySelectorAll('.hl.lean .tactic-state').length,
                outputs: document.querySelectorAll('.lean-output').length,
                docHovers: document.querySelectorAll('.hl.lean [data-verso-hover]').length,
                nestedStates: document.querySelectorAll('.hl.lean .has-info.warning .tactic-state').length,
            })"""
        )
        # sorry definition, deprecated use, and a sorry proof
        assert counts["warning"] >= 3, counts
        # the flag_proof theorem nests proof states inside a warning span
        assert counts["nestedStates"] >= 1, counts
        # #eval and #check hovers
        assert counts["information"] >= 2, counts
        assert counts["tactics"] >= 2, counts
        assert counts["tacticStates"] >= 2, counts
        # #eval and #check output blocks
        assert counts["outputs"] >= 2, counts
        assert counts["docHovers"] >= 1, counts

    def test_expected_error_block_attaches_diagnostic(self, server: str, page: Page):
        """The `+error` code block's diagnostic is attached to the failing code. Lean
        re-logs expected errors as silent information messages, so the span carries
        information severity."""
        page.goto(f"{server}{GALLERY}")
        page.wait_for_load_state("networkidle")
        span = page.locator(".hl.lean .has-info", has_text='"three"').last
        assert span.count() > 0
        msg = span.locator(".verso-message").first.inner_text()
        assert "Type mismatch" in msg

    def test_proof_state_css_nests_under_warning(self, server: str, page: Page):
        """Warning code colors inherit into a warning-wrapped proof but stop at the
        proof states nested inside it, which use their own variables."""
        page.add_init_script(
            """document.addEventListener('DOMContentLoaded', () => {
                const s = document.documentElement.style;
                s.setProperty('--verso-code-warning-color', 'rgb(10, 20, 30)');
                s.setProperty('--verso-tactic-state-color', 'rgb(1, 2, 3)');
                s.setProperty('--verso-tactic-state-bg-color', 'rgb(4, 5, 6)');
            })"""
        )
        page.goto(f"{server}{GALLERY}")
        page.wait_for_load_state("networkidle")
        result = page.evaluate(
            """() => {
                const span = document.querySelector('.hl.lean .has-info.warning:has(.tactic-state)');
                const label = span.querySelector('.tactic > label');
                const state = span.querySelector('.tactic-state');
                return {
                    spanColor: getComputedStyle(span).color,
                    labelColor: getComputedStyle(label).color,
                    stateColor: getComputedStyle(state).color,
                    stateBg: getComputedStyle(state).backgroundColor,
                };
            }"""
        )
        assert result["spanColor"] == "rgb(10, 20, 30)"
        assert result["labelColor"] == "rgb(10, 20, 30)"
        assert result["stateColor"] == "rgb(1, 2, 3)"
        assert result["stateBg"] == "rgb(4, 5, 6)"

    def test_warning_hover_uses_warning_theme(self, server: str, page: Page):
        page.goto(f"{server}{GALLERY}")
        page.wait_for_load_state("networkidle")
        page.locator(".hl.lean .has-info.warning").first.hover()
        box = page.locator(".tippy-box[data-theme~='warning']").first
        box.wait_for(state="visible")
        assert "declaration uses" in box.inner_text()

    def test_warning_hover_highlights_whole_span(self, server: str, page: Page):
        """Hovering warning-carrying code shows the warning hover background across the
        whole span; the token hover highlight is removed so it reads as one region."""
        page.goto(f"{server}{GALLERY}")
        page.wait_for_load_state("networkidle")
        require_hover_media(page)
        token = page.locator(".hl.lean .has-info.warning > .token").first
        token.hover()
        span_bg = page.evaluate(
            "() => getComputedStyle(document.querySelector('.hl.lean .has-info.warning')).backgroundColor"
        )
        token_bg = page.evaluate(
            "() => getComputedStyle(document.querySelector('.hl.lean .has-info.warning > .token')).backgroundColor"
        )
        assert span_bg == "rgb(255, 243, 205)"
        assert token_bg == "rgba(0, 0, 0, 0)"

    def test_sorry_name_shows_single_merged_hover(self, server: str, page: Page):
        """The warning span around a sorry definition's name shares the name token's
        extent, so one tooltip shows both the warning and the documentation."""
        page.goto(f"{server}{GALLERY}")
        page.wait_for_load_state("networkidle")
        page.locator(".hl.lean .has-info.warning > .token").first.hover()
        box = page.locator(".tippy-box").first
        box.wait_for(state="visible")
        page.wait_for_timeout(400)
        boxes = page.locator(".tippy-box")
        assert boxes.count() == 1
        text = boxes.first.inner_text()
        assert "declaration uses" in text
        assert "Sorts a list, eventually." in text
        # The warning keeps its severity accent, distinguishing it from the documentation
        accent = page.evaluate(
            """() => {
                const msg = document.querySelector('.tippy-box .hover-info.messages > code.warning');
                const style = getComputedStyle(msg);
                return { width: style.borderLeftWidth, color: style.borderLeftColor };
            }"""
        )
        assert accent["width"] != "0px"
        assert accent["color"] == "rgb(255, 243, 205)"
        # The message block is separated from the documentation below it
        margin = page.evaluate(
            "() => getComputedStyle(document.querySelector('.tippy-box .hl.lean.mixed > .hover-info.messages')).marginBottom"
        )
        assert margin != "0px"

    def test_tooltip_links_not_underlined(self, server: str, page: Page):
        """Constant links inside tooltip content show no underline until hovered."""
        page.goto(f"{server}{GALLERY}")
        page.wait_for_load_state("networkidle")
        # The deprecated use site's tooltip message links to both constants.
        page.locator(
            ".hl.lean .has-info.warning > a > .token", has_text="oldGallerySort"
        ).first.hover()
        box = page.locator(".tippy-box").first
        box.wait_for(state="visible")
        assert box.locator("a").count() > 0
        deco = page.evaluate(
            "() => getComputedStyle(document.querySelector('.tippy-box a')).textDecorationLine"
        )
        assert deco == "none"

    def test_nested_message_regions(self, server: str, page: Page):
        """A warning region nested inside an informational region keeps its own text and
        underline colors, and the informational region continues past it."""
        page.add_init_script(
            """document.addEventListener('DOMContentLoaded', () => {
                const s = document.documentElement.style;
                s.setProperty('--verso-code-info-color', 'rgb(1, 2, 3)');
                s.setProperty('--verso-code-warning-color', 'rgb(4, 5, 6)');
                s.setProperty('--verso-info-indicator-color', 'rgb(7, 8, 9)');
                s.setProperty('--verso-warning-indicator-color', 'rgb(10, 11, 12)');
            })"""
        )
        page.goto(f"{server}{GALLERY}")
        page.wait_for_load_state("networkidle")
        result = page.evaluate(
            """() => {
                const outer = document.querySelector(
                    '.hl.lean .has-info.information:has(.has-info.warning)');
                if (!outer) return null;
                const inner = outer.querySelector('.has-info.warning');
                const tokenIn = (region) =>
                    Array.from(region.querySelectorAll('.token')).find(t =>
                        t.closest('.has-info') === region && !t.closest('.tactic-state'));
                const codeText = (el) => {
                    const c = el.cloneNode(true);
                    c.querySelectorAll('.hover-container, .tactic-state').forEach(x => x.remove());
                    return c.textContent;
                };
                return {
                    outerColor: getComputedStyle(outer).color,
                    innerColor: getComputedStyle(inner).color,
                    outerUnderline: getComputedStyle(tokenIn(outer)).textDecorationColor,
                    innerUnderline: getComputedStyle(tokenIn(inner)).textDecorationColor,
                    outerText: codeText(outer),
                };
            }"""
        )
        assert result is not None, "expected a warning region nested in an info region"
        assert result["outerColor"] == "rgb(1, 2, 3)"
        assert result["innerColor"] == "rgb(4, 5, 6)"
        assert result["outerUnderline"] == "rgb(7, 8, 9)"
        assert result["innerUnderline"] == "rgb(10, 11, 12)"
        # The informational region includes the branch after the warning
        assert "succ" in result["outerText"]

    def test_hover_highlight_matches_tooltip(self, server: str, page: Page):
        """Hovering a documented token inside a message region shows the token's tooltip,
        so only the token is highlighted: the region and the enclosing tactic label are
        not."""
        page.goto(f"{server}{GALLERY}")
        page.wait_for_load_state("networkidle")
        token = page.locator(
            ".hl.lean .has-info.warning .token", has_text="flag_proof"
        ).first
        token.hover()
        box = page.locator(".tippy-box").first
        box.wait_for(state="visible")
        assert "Runs a tactic sequence" in box.inner_text()
        # The highlight assertions read CSS that is guarded by @media (hover: hover).
        require_hover_media(page)
        result = page.evaluate(
            """() => {
                const token = Array.from(document.querySelectorAll('.hl.lean .has-info.warning .token'))
                    .find(t => t.textContent === 'flag_proof');
                const label = token.closest('label');
                return {
                    token: getComputedStyle(token).backgroundColor,
                    label: label ? getComputedStyle(label).backgroundColor : null,
                    region: getComputedStyle(token.closest('.has-info')).backgroundColor,
                };
            }"""
        )
        assert result["token"] == "rgb(238, 238, 238)"
        assert result["label"] in (None, "rgba(0, 0, 0, 0)")
        assert result["region"] == "rgba(0, 0, 0, 0)"

    def test_same_range_messages_share_a_region(self, server: str, page: Page):
        """Messages of different severities with exactly the same range share one region,
        styled by the most severe message. Its tooltip carries both messages, each with
        its own severity accent."""
        page.goto(f"{server}{GALLERY}")
        page.wait_for_load_state("networkidle")
        result = page.evaluate(
            """() => {
                const span = Array.from(document.querySelectorAll('.hl.lean .has-info.warning'))
                    .find(s =>
                        s.querySelector(':scope > .hover-container code.verso-message.warning') &&
                        s.querySelector(':scope > .hover-container code.verso-message.information'));
                if (!span || !span._tippy) return null;
                const inst = span._tippy;
                inst.show();
                const box = inst.popper.querySelector('.tippy-box');
                const accent = (sel) => {
                    const st = getComputedStyle(box.querySelector(sel));
                    return { width: st.borderLeftWidth, color: st.borderLeftColor };
                };
                const res = {
                    theme: box.dataset.theme,
                    warn: accent('code.verso-message.warning'),
                    info: accent('code.verso-message.information'),
                };
                inst.hide();
                return res;
            }"""
        )
        assert result is not None, "expected a region carrying both severities"
        assert "warning" in result["theme"]
        assert result["warn"]["width"] != "0px"
        assert result["warn"]["color"] == "rgb(255, 243, 205)"
        assert result["info"]["width"] != "0px"
        assert result["info"]["color"] == "rgb(207, 226, 255)"

    def test_enclosing_tooltip_hides_nested_tooltip(self, server: str, page: Page):
        """Showing an enclosing region's tooltip hides a tooltip that is already visible
        on content nested inside it, so only one tooltip is on screen at a time."""
        page.goto(f"{server}{GALLERY}")
        page.wait_for_load_state("networkidle")
        # The #check command's information span contains the documented List.length token.
        shown = page.evaluate(
            """() => {
                const span = Array.from(document.querySelectorAll('.hl.lean .has-info.information'))
                    .find(s => s._tippy && s.querySelector('[data-verso-hover]')?._tippy);
                if (!span) return false;
                window._nestedTooltips = { span, tok: span.querySelector('[data-verso-hover]') };
                window._nestedTooltips.tok._tippy.show();
                return true;
            }"""
        )
        assert shown, "expected an information span containing a documented token"
        # The nested tooltip only registers as visible once its transition finishes.
        page.wait_for_function("() => window._nestedTooltips.tok._tippy.state.isShown")
        result = page.evaluate(
            """() => {
                const { span, tok } = window._nestedTooltips;
                span._tippy.show();
                return {
                    span: span._tippy.state.isVisible,
                    tok: tok._tippy.state.isVisible,
                };
            }"""
        )
        assert result["span"]
        assert not result["tok"]

    def test_tooltip_follows_toggle_under_pointer(self, server: str, page: Page):
        """Clicking a proof-state label nested in a warning span switches the tooltip in
        place: expanding shows the warning span's tooltip, collapsing shows the proof
        state again. The pointer never leaves the span, so no hover event fires; the
        toggle itself must update the tooltip."""
        page.goto(f"{server}{GALLERY}")
        page.wait_for_load_state("networkidle")
        label = page.locator(".hl.lean .has-info.warning .tactic > label").first
        # Aim at whitespace inside the label: hovering the label's center would land on
        # whichever token the browser's font metrics put there, and a documented token
        # would rightly claim the tooltip for itself once the region is expanded.
        target = label.locator(".inter-text").first
        target.hover()
        page.locator(".tippy-box[data-theme~='tactic']").first.wait_for(state="visible")
        target.click()
        page.locator(".tippy-box[data-theme~='warning']").first.wait_for(
            state="visible"
        )
        target.click()
        page.locator(".tippy-box[data-theme~='tactic']").first.wait_for(state="visible")

    def test_message_tooltip_after_expanding_proof(self, server: str, page: Page):
        """A message span inside a collapsed proof gains its tooltip when the proof is
        expanded."""
        page.goto(f"{server}{GALLERY}")
        page.wait_for_load_state("networkidle")
        result = page.evaluate(
            """() => {
                const span = Array.from(document.querySelectorAll('.hl.lean .has-info.warning'))
                    .find(s => s.textContent.includes('oldGallerySort') &&
                        s.closest('.tactic') && s.closest('.tactic') !== s);
                if (!span) return null;
                const before = !!span._tippy;
                const toggle = span.closest('.tactic').querySelector(':scope > input.tactic-toggle');
                toggle.click();
                return { before, after: !!span._tippy };
            }"""
        )
        assert result is not None, "expected a warning span inside a proof"
        assert not result["before"]
        assert result["after"]

    def test_no_duplicate_proof_states(self, server: str, page: Page):
        """No proof state appears twice with the same goals at the same position."""
        page.goto(f"{server}{GALLERY}")
        page.wait_for_load_state("networkidle")
        keys = page.evaluate(
            """() => Array.from(document.querySelectorAll('input.tactic-toggle[id]'))
                .map(e => e.id.split('-').slice(0, -1).join('-'))"""
        )
        assert len(keys) == len(set(keys)), keys

    def test_tactic_hover_uses_tactic_theme(self, server: str, page: Page):
        page.goto(f"{server}{GALLERY}")
        page.wait_for_load_state("networkidle")
        page.locator(".hl.lean .tactic > label").first.hover()
        box = page.locator(".tippy-box[data-theme~='tactic']").first
        box.wait_for(state="visible")
