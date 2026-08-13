"""Checks that the documented --verso-* CSS variables drive the computed styles of
Verso's code output.

Each test sets variables to distinctive values on the root element, injects synthetic
markup reproducing the nestings that occur in generated pages (severity spans around
tokens, proof states nested in severity spans, message popups, output blocks, tooltip
boxes), and asserts the resulting computed styles. Variables are set before the markup
is injected so the elements' styles are computed from the overridden values.
"""

import pytest
from playwright.sync_api import Page

from hover_media import require_hover_media

# (CSS class, variable infix, tippy theme token) for each severity
SEVERITIES = [
    ("error", "error", "error"),
    ("warning", "warning", "warning"),
    ("information", "info", "info"),
]


def markup(cls: str, theme: str) -> str:
    return f"""
    <div class="hl lean block" id="vt-root">
      <span class="has-info {cls}" id="vt-span">
        <span class="hover-container">
          <span class="hover-info messages">
            <code class="verso-message {cls}" id="vt-msg">msg</code>
          </span>
        </span>
        <span class="token const" id="vt-token">tok</span>
        <span class="tactic">
          <label id="vt-label">simp</label>
          <span class="tactic-state" id="vt-state">goal</span>
        </span>
      </span>
    </div>
    <pre class="lean-output {cls}" id="vt-output">out</pre>
    <div class="tippy-box" data-theme="{theme} message" data-placement="top" id="vt-tippy">tip</div>
    <div class="tippy-box" data-theme="lean" data-placement="top" id="vt-tippy-lean">doc</div>
    <div class="tippy-box" data-theme="tactic" data-placement="top" id="vt-tippy-tactic">state</div>
    """


def setup(page: Page, server: str, vars: dict, cls: str, theme: str):
    page.goto(f"{server}/LitConfig/")
    page.wait_for_load_state("networkidle")
    page.evaluate(
        """vars => {
            for (const [k, v] of Object.entries(vars)) {
                document.documentElement.style.setProperty(k, v);
            }
        }""",
        vars,
    )
    page.evaluate(
        "html => document.body.insertAdjacentHTML('beforeend', html)",
        markup(cls, theme),
    )


def computed(page: Page, selector: str, prop: str) -> str:
    return page.evaluate(
        "([sel, prop]) => getComputedStyle(document.querySelector(sel)).getPropertyValue(prop)",
        [selector, prop],
    )


def computed_pseudo(page: Page, selector: str, pseudo: str, prop: str) -> str:
    return page.evaluate(
        "([sel, pseudo, prop]) => getComputedStyle(document.querySelector(sel), pseudo).getPropertyValue(prop)",
        [selector, pseudo, prop],
    )


class TestSeverityVariables:
    @pytest.mark.parametrize(("cls", "v", "theme"), SEVERITIES)
    def test_affected_code(self, server: str, page: Page, cls: str, v: str, theme: str):
        setup(
            page,
            server,
            {
                f"--verso-code-{v}-color": "rgb(10, 20, 30)",
                f"--verso-code-{v}-bg-color": "rgb(40, 50, 60)",
                f"--verso-code-{v}-hover-bg-color": "rgb(70, 80, 90)",
                f"--verso-{v}-indicator-color": "rgb(100, 110, 120)",
            },
            cls,
            theme,
        )
        assert computed(page, "#vt-span", "color") == "rgb(10, 20, 30)"
        assert computed(page, "#vt-span", "background-color") == "rgb(40, 50, 60)"
        # The wavy underline marking the message's presence
        assert (
            computed(page, "#vt-token", "text-decoration-color") == "rgb(100, 110, 120)"
        )
        # The hover background reads CSS that is guarded by @media (hover: hover).
        require_hover_media(page)
        page.locator("#vt-span").hover()
        assert computed(page, "#vt-span", "background-color") == "rgb(70, 80, 90)"

    @pytest.mark.parametrize(("cls", "v", "theme"), SEVERITIES)
    def test_message_and_output(
        self, server: str, page: Page, cls: str, v: str, theme: str
    ):
        setup(
            page,
            server,
            {
                f"--verso-message-{v}-color": "rgb(130, 140, 150)",
                f"--verso-output-{v}-color": "rgb(160, 170, 180)",
            },
            cls,
            theme,
        )
        assert computed(page, "#vt-msg", "color") == "rgb(130, 140, 150)"
        assert computed(page, "#vt-output", "border-left-color") == "rgb(160, 170, 180)"

    @pytest.mark.parametrize(("cls", "v", "theme"), SEVERITIES)
    def test_tooltip_chrome(
        self, server: str, page: Page, cls: str, v: str, theme: str
    ):
        setup(
            page,
            server,
            {
                f"--verso-tooltip-{v}-color": "rgb(190, 200, 210)",
                f"--verso-tooltip-{v}-bg-color": "rgb(220, 230, 240)",
                f"--verso-tooltip-{v}-border-color": "rgb(5, 15, 25)",
            },
            cls,
            theme,
        )
        assert computed(page, "#vt-tippy", "color") == "rgb(190, 200, 210)"
        assert computed(page, "#vt-tippy", "background-color") == "rgb(220, 230, 240)"
        assert computed(page, "#vt-tippy", "border-top-color") == "rgb(5, 15, 25)"
        # The no-script message box uses the same tooltip colors
        assert computed(page, "#vt-msg", "background-color") == "rgb(220, 230, 240)"
        assert computed(page, "#vt-msg", "border-left-color") == "rgb(5, 15, 25)"


class TestNestedSeverityHover:
    def test_nearest_severity_hover_colors_win(self, server: str, page: Page):
        """The hover highlight of a message span comes from its own severity's variables,
        for a span nested inside one of another severity as well as for the outer span.
        The single hover rule reads `--verso--region-hover-*`, which inherit, so each
        span's own severity assignment must be the one in effect."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")
        require_hover_media(page)
        page.evaluate(
            """() => {
                const s = document.documentElement.style;
                s.setProperty('--verso-code-info-bg-color', 'rgb(40, 50, 60)');
                s.setProperty('--verso-code-info-hover-bg-color', 'rgb(70, 80, 90)');
                s.setProperty('--verso-code-warning-bg-color', 'rgb(61, 62, 63)');
                s.setProperty('--verso-code-warning-hover-bg-color', 'rgb(91, 92, 93)');
            }"""
        )
        page.evaluate(
            """html => document.body.insertAdjacentHTML('beforeend', html)""",
            '<div class="hl lean block" id="vt-nested-root">'
            '<span class="has-info information" id="vt-outer">outer text '
            '<span class="has-info warning" id="vt-inner">inner</span>'
            "</span></div>",
        )
        # Hovering the nested warning span: its own hover colors, while the outer span
        # keeps its base background because the nested span's tooltip is the one shown.
        page.locator("#vt-inner").hover()
        assert computed(page, "#vt-inner", "background-color") == "rgb(91, 92, 93)"
        assert computed(page, "#vt-outer", "background-color") == "rgb(40, 50, 60)"
        # Hovering the outer span's own text: the outer span's hover colors.
        box = page.locator("#vt-outer").bounding_box()
        page.mouse.move(box["x"] + 5, box["y"] + box["height"] / 2)
        assert computed(page, "#vt-outer", "background-color") == "rgb(70, 80, 90)"
        assert computed(page, "#vt-inner", "background-color") == "rgb(61, 62, 63)"


class TestTacticStateIsland:
    def test_severity_color_stops_at_proof_state(self, server: str, page: Page):
        """A severity code color inherits into the affected code but not into a proof
        state nested within it, which uses its own variables."""
        setup(
            page,
            server,
            {
                "--verso-code-error-color": "rgb(10, 20, 30)",
                "--verso-tactic-state-color": "rgb(1, 2, 3)",
                "--verso-tactic-state-bg-color": "rgb(4, 5, 6)",
                "--verso-tactic-state-border-color": "rgb(7, 8, 9)",
            },
            "error",
            "error",
        )
        # The tactic's label is affected code and inherits the severity color
        assert computed(page, "#vt-label", "color") == "rgb(10, 20, 30)"
        # The proof state does not
        assert computed(page, "#vt-state", "color") == "rgb(1, 2, 3)"
        assert computed(page, "#vt-state", "background-color") == "rgb(4, 5, 6)"
        assert computed(page, "#vt-state", "border-top-color") == "rgb(7, 8, 9)"


# (tippy theme, background variable, border variable) for every themed tooltip
ARROW_THEMES = [
    (
        "error message",
        "--verso-tooltip-error-bg-color",
        "--verso-tooltip-error-border-color",
    ),
    (
        "warning message",
        "--verso-tooltip-warning-bg-color",
        "--verso-tooltip-warning-border-color",
    ),
    (
        "info message",
        "--verso-tooltip-info-bg-color",
        "--verso-tooltip-info-border-color",
    ),
    ("lean", "--verso-tooltip-bg-color", "--verso-tooltip-border-color"),
    ("tactic", "--verso-tactic-state-bg-color", "--verso-tactic-state-border-color"),
]

PLACEMENTS = ["top", "bottom", "left", "right"]


def arrow_markup(theme: str) -> str:
    return "".join(
        f'<div class="tippy-box" data-theme="{theme}" data-placement="{p}" id="vt-box-{p}">'
        f'<div class="tippy-arrow" id="vt-arrow-{p}"></div></div>'
        for p in PLACEMENTS
    )


class TestTooltipArrows:
    """The arrow of a tooltip is filled with the tooltip's background color and outlined
    with its border color, at every placement. Tippy paints the fill from the arrow
    element's `color` and the outline from the box's border color, so each theme sets
    only `color` on its arrow."""

    @pytest.mark.parametrize(("theme", "bg_var", "border_var"), ARROW_THEMES)
    def test_arrow_follows_variables(
        self, server: str, page: Page, theme: str, bg_var: str, border_var: str
    ):
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")
        page.evaluate(
            """([bgVar, borderVar]) => {
                document.documentElement.style.setProperty(bgVar, 'rgb(21, 22, 23)');
                document.documentElement.style.setProperty(borderVar, 'rgb(31, 32, 33)');
            }""",
            [bg_var, border_var],
        )
        page.evaluate(
            "html => document.body.insertAdjacentHTML('beforeend', html)",
            arrow_markup(theme),
        )
        for p in PLACEMENTS:
            fill = computed_pseudo(
                page, f"#vt-arrow-{p}", "::before", f"border-{p}-color"
            )
            outline = computed_pseudo(
                page, f"#vt-arrow-{p}", "::after", f"border-{p}-color"
            )
            assert fill == "rgb(21, 22, 23)", f"{theme} {p} arrow fill"
            assert outline == "rgb(31, 32, 33)", f"{theme} {p} arrow outline"

    def test_arrow_matches_tooltip_by_default(self, server: str, page: Page):
        """With no customization, every theme's arrow fill equals its box background and
        its outline equals its box border, at every placement."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")
        for theme, _, _ in ARROW_THEMES:
            page.evaluate(
                "() => document.querySelectorAll('.tippy-box').forEach(e => e.remove())"
            )
            page.evaluate(
                "html => document.body.insertAdjacentHTML('beforeend', html)",
                arrow_markup(theme),
            )
            for p in PLACEMENTS:
                box_bg = computed(page, f"#vt-box-{p}", "background-color")
                box_border = computed(page, f"#vt-box-{p}", f"border-{p}-color")
                fill = computed_pseudo(
                    page, f"#vt-arrow-{p}", "::before", f"border-{p}-color"
                )
                outline = computed_pseudo(
                    page, f"#vt-arrow-{p}", "::after", f"border-{p}-color"
                )
                assert fill == box_bg, f"{theme} {p}: fill {fill} != box bg {box_bg}"
                assert outline == box_border, (
                    f"{theme} {p}: outline {outline} != box border {box_border}"
                )

    def test_real_tooltip_arrow(self, server: str, page: Page):
        """Hovering a real token produces a tooltip whose arrow fill matches its
        background."""
        page.goto(f"{server}/LitConfig/Core/")
        page.wait_for_load_state("networkidle")
        token = page.locator(".hl.lean .const.token").first
        token.hover()
        box = page.locator(".tippy-box").first
        box.wait_for(state="visible")
        page.wait_for_function(
            "() => document.querySelector('.tippy-box')?.getAttribute('data-placement')"
        )
        placement = box.get_attribute("data-placement").split("-")[0]
        result = page.evaluate(
            """side => {
                const box = document.querySelector('.tippy-box');
                const arrow = box.querySelector('.tippy-arrow');
                return {
                    boxBg: getComputedStyle(box).backgroundColor,
                    fill: getComputedStyle(arrow, '::before').getPropertyValue('border-' + side + '-color'),
                };
            }""",
            placement,
        )
        assert result["fill"] == result["boxBg"]


class TestDerivedDefaults:
    def test_generic_tooltip_colors_flow_to_severities(self, server: str, page: Page):
        setup(
            page,
            server,
            {
                "--verso-tooltip-color": "rgb(11, 12, 13)",
                "--verso-tooltip-bg-color": "rgb(14, 15, 16)",
            },
            "warning",
            "warning",
        )
        # Severity tooltips default to the generic tooltip colors
        assert computed(page, "#vt-tippy", "color") == "rgb(11, 12, 13)"
        assert computed(page, "#vt-tippy", "background-color") == "rgb(14, 15, 16)"
        # The documentation tooltip uses them directly
        assert computed(page, "#vt-tippy-lean", "color") == "rgb(11, 12, 13)"
        assert computed(page, "#vt-tippy-lean", "background-color") == "rgb(14, 15, 16)"

    def test_output_bar_defaults_to_indicator(self, server: str, page: Page):
        setup(
            page,
            server,
            {"--verso-warning-indicator-color": "rgb(17, 18, 19)"},
            "warning",
            "warning",
        )
        assert computed(page, "#vt-output", "border-left-color") == "rgb(17, 18, 19)"

    def test_tactic_tooltip_uses_proof_state_colors(self, server: str, page: Page):
        setup(
            page,
            server,
            {
                "--verso-tactic-state-color": "rgb(1, 2, 3)",
                "--verso-tactic-state-bg-color": "rgb(4, 5, 6)",
                "--verso-tactic-state-border-color": "rgb(7, 8, 9)",
            },
            "warning",
            "warning",
        )
        assert computed(page, "#vt-tippy-tactic", "color") == "rgb(1, 2, 3)"
        assert computed(page, "#vt-tippy-tactic", "background-color") == "rgb(4, 5, 6)"
        assert computed(page, "#vt-tippy-tactic", "border-top-color") == "rgb(7, 8, 9)"
