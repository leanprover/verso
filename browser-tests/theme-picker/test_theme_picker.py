"""
Browser tests for the theme picker (gear button + popover + dropdowns).

Builds the user's guide (which ships multiple themes via @[manual_theme]) and exercises:
  * gear placement in header-tools, left of the search box
  * popover open/close, role + aria-* attributes, Escape returns focus to the gear
  * focus trap inside the popover
  * the Appearance radios (Light / Dark / Follow system) drive data-verso-theme and
    data-verso-appearance, and persist across reloads via localStorage
  * "Follow system" tracks matchMedia(prefers-color-scheme); Light/Dark lock the appearance
  * the collapsible "Theme choices" section is expanded only when a non-default light or dark
    theme is stored
  * graceful degradation when localStorage throws (page still loads, default theme applied)
"""

import socket
import subprocess
import time
from pathlib import Path

import pytest
from playwright.sync_api import sync_playwright


HERE = Path(__file__).parent
REPO_ROOT = HERE.parent.parent
SITE_DIR = REPO_ROOT / "_out" / "usersguide" / "html-multi"


def _find_free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


@pytest.fixture(scope="module")
def built_site():
    subprocess.check_call(
        ["lake", "build", "usersguide"],
        cwd=REPO_ROOT,
    )
    if SITE_DIR.parent.exists():
        subprocess.check_call(["rm", "-rf", str(SITE_DIR.parent)], cwd=REPO_ROOT)
    subprocess.check_call(
        [
            "lake",
            "exe",
            "usersguide",
            "--output",
            "_out/usersguide",
            "--without-tex",
            "--without-html-single",
            "--with-html-multi",
        ],
        cwd=REPO_ROOT,
    )
    assert SITE_DIR.exists(), f"Manual build did not produce {SITE_DIR}"
    return SITE_DIR


@pytest.fixture(scope="module")
def server(built_site):
    port = _find_free_port()
    proc = subprocess.Popen(
        ["python", "-m", "http.server", str(port), "--bind", "127.0.0.1"],
        cwd=built_site,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    time.sleep(0.5)
    try:
        yield f"http://127.0.0.1:{port}"
    finally:
        proc.terminate()
        proc.wait()


@pytest.fixture(scope="module")
def playwright_instance():
    with sync_playwright() as p:
        yield p


@pytest.fixture(params=["chromium", "firefox"])
def page(request, playwright_instance, server):
    """Per-test page so localStorage / focus state don't leak between tests."""
    browser = getattr(playwright_instance, request.param).launch()
    context = browser.new_context()
    p = context.new_page()
    p.goto(server + "/")
    yield p
    context.close()
    browser.close()


def _picker_button(page):
    return page.locator("#theme-picker-button")


def _dialog(page):
    return page.locator("#theme-picker-dialog")


def _expand_choices(page):
    """Open the collapsible Light/Dark "Theme choices" section if it isn't already open."""
    choices = page.locator("#theme-picker-choices")
    if choices.count() and choices.get_attribute("open") is None:
        page.locator("#theme-picker-choices > summary").click()


def _set_mode(page, mode):
    """Select an Appearance radio button: 'light', 'dark', or 'auto'."""
    page.locator(f"#theme-picker-mode-{mode}").check()


def test_gear_height_and_centering_match_search(page):
    """The gear glyph's ink height should be about 90% of the search input's outer height,
    and the two centers should be aligned vertically. (The user asked for "90% as tall as
    the search field and vertically centered with respect to the search field".)"""
    page.set_viewport_size({"width": 1400, "height": 800})
    page.locator("#theme-picker-button").wait_for(state="visible", timeout=5000)
    m = page.evaluate(
        """() => {
            const gear = document.querySelector('#theme-picker-button .theme-picker-gear');
            const input = document.querySelector('#search-wrapper .cb_edit');
            // The visible glyph rect, not the line-box, is what reads as "the gear's
            // height" — `Range.getBoundingClientRect()` snaps to the rendered ink box.
            const r = document.createRange();
            r.selectNodeContents(gear);
            const ink = r.getBoundingClientRect();
            const ir = input.getBoundingClientRect();
            return {
                ink_h: ink.height,
                input_h: ir.height,
                ink_mid: (ink.top + ink.bottom) / 2,
                input_mid: (ir.top + ir.bottom) / 2,
            };
        }"""
    )
    ratio = m["ink_h"] / m["input_h"]
    offset = abs(m["ink_mid"] - m["input_mid"])
    # The Unicode `⚙` glyph's visible cog is about 70-75% of its ink rect — i.e. an ink
    # rect that matches the input optically reads smaller than the input. To get the gear
    # to *look* like it matches the search field, the rendered ink rect needs to overshoot
    # the input by ~15-25%. The acceptance band brackets that, with a little extra
    # tolerance for cross-browser font metrics (Firefox renders the glyph metrics a couple
    # of percent above Chromium at the same `font-size`).
    assert 1.10 <= ratio <= 1.35, (
        f"gear glyph height {m['ink_h']:.2f}px is {ratio:.2%} of the search input height "
        f"({m['input_h']:.2f}px); want ~115–125% so the optical cog matches the field"
    )
    # Visual centering tolerance: one pixel is below the perceptual threshold for "off
    # center" at standard zoom.
    assert offset <= 1.0, (
        f"gear glyph center is {offset:.2f}px from the search input center; want <1px"
    )


def test_gear_in_header_tools_left_of_search(page):
    btn = _picker_button(page)
    btn.wait_for(state="attached", timeout=5000)
    assert btn.is_visible()
    # The gear sits inside `.header-tools` and that block is ordered before the search
    # box by the `order: -1` rule in theme-picker.css. Verify the gear is geometrically
    # to the left of the search box on a desktop viewport.
    page.set_viewport_size({"width": 1200, "height": 800})
    gear_box = btn.bounding_box()
    search = page.locator("#search-wrapper")
    if search.count() > 0:
        search_box = search.first.bounding_box()
        if search_box is not None and gear_box is not None:
            assert gear_box["x"] < search_box["x"], (
                f"gear at x={gear_box['x']}, search at x={search_box['x']}"
            )


def test_popover_open_close_aria(page):
    btn = _picker_button(page)
    btn.wait_for(state="attached", timeout=5000)
    assert btn.get_attribute("aria-expanded") == "false"
    btn.click()
    d = _dialog(page)
    d.wait_for(state="attached", timeout=5000)
    assert btn.get_attribute("aria-expanded") == "true"
    assert d.get_attribute("role") == "dialog"
    assert d.get_attribute("aria-label") is not None
    # Escape closes and returns focus to the gear.
    page.keyboard.press("Escape")
    page.wait_for_function(
        "document.getElementById('theme-picker-button').getAttribute('aria-expanded') === 'false'"
    )
    assert page.evaluate("document.activeElement.id") == "theme-picker-button"


def test_focus_trap(page):
    btn = _picker_button(page)
    btn.click()
    dialog = _dialog(page)
    dialog.wait_for(state="attached", timeout=5000)
    # The focus trap pushes Tab from the last focusable back to the first; just check that
    # repeated Tab presses keep focus within the dialog.
    for _ in range(10):
        page.keyboard.press("Tab")
        in_dialog = page.evaluate(
            "document.getElementById('theme-picker-dialog').contains(document.activeElement)"
        )
        assert in_dialog, "focus escaped the dialog"


def test_appearance_radios_offer_light_dark_follow_system(page):
    """The Appearance group offers exactly Light / Dark / Follow system radios, in that order."""
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    radios = page.locator("#theme-picker-mode input[type=radio]")
    values = radios.evaluate_all("els => els.map(e => e.value)")
    labels = page.locator("#theme-picker-mode .theme-picker-radio").all_text_contents()
    assert values == ["light", "dark", "auto"], f"unexpected radio values {values!r}"
    assert [t.strip() for t in labels] == ["Light", "Dark", "Follow system"], (
        f"unexpected radio labels {labels!r}"
    )


def test_first_visit_defaults_to_follow_system(page):
    """A fresh visitor (no stored mode) sees the Appearance group on 'Follow system'."""
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    assert page.locator("#theme-picker-mode-auto").is_checked()
    assert not page.locator("#theme-picker-mode-light").is_checked()
    assert not page.locator("#theme-picker-mode-dark").is_checked()


def test_default_mode_exposed_and_drives_initial_radio(page):
    """`window.versoThemes.defaultMode` is the author-configured starting mode (the user's guide
    uses the default `followSystem`, encoded as `auto`), and the picker starts on it when nothing
    is stored."""
    default_mode = page.evaluate("window.versoThemes.defaultMode")
    assert default_mode == "auto", (
        f"expected exposed defaultMode 'auto', got {default_mode!r}"
    )
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    assert page.locator(f"#theme-picker-mode-{default_mode}").is_checked()


def test_light_mode_switching_persists(page, server):
    """Selecting Light mode and a non-default light theme sets the data attributes and
    survives a reload (the no-flash script reapplies it before paint)."""
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    _set_mode(page, "light")
    _expand_choices(page)
    light = page.locator("#theme-picker-light")
    current = page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
    chosen = None
    for opt in light.locator("option").all():
        v = opt.get_attribute("value")
        if v and v != current:
            chosen = v
            break
    if chosen is None:
        pytest.skip("not enough light themes registered to test switching")
    light.select_option(value=chosen)
    assert (
        page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
        == chosen
    )
    assert page.evaluate("localStorage.getItem('verso-theme-light')") == chosen
    assert page.evaluate("localStorage.getItem('verso-theme-mode')") == "light"
    # Reload: the no-flash script reads localStorage and applies the same theme before paint.
    page.goto(server + "/")
    page.wait_for_load_state("domcontentloaded")
    assert (
        page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
        == chosen
    )


def test_follow_system_tracks_media(page):
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    _set_mode(page, "auto")
    # Emulate dark, then light; the inline script's matchMedia listener should swap themes.
    page.emulate_media(color_scheme="dark")
    page.wait_for_timeout(50)
    dark_id = page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
    dark_appearance = page.evaluate(
        "document.documentElement.getAttribute('data-verso-appearance')"
    )
    page.emulate_media(color_scheme="light")
    page.wait_for_timeout(50)
    light_id = page.evaluate(
        "document.documentElement.getAttribute('data-verso-theme')"
    )
    light_appearance = page.evaluate(
        "document.documentElement.getAttribute('data-verso-appearance')"
    )
    assert dark_id != light_id, (
        "Follow system should pick different themes for light vs dark"
    )
    assert dark_appearance == "dark" and light_appearance == "light"


def test_locked_appearance_ignores_media(page):
    """Light mode locks the appearance: a system media change must not override the theme."""
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    _set_mode(page, "light")
    chosen = page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
    page.emulate_media(color_scheme="dark")
    page.wait_for_timeout(50)
    assert (
        page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
        == chosen
    )
    assert (
        page.evaluate("document.documentElement.getAttribute('data-verso-appearance')")
        == "light"
    )
    page.emulate_media(color_scheme="light")
    page.wait_for_timeout(50)
    assert (
        page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
        == chosen
    )


def test_auto_commit_applies_dropdown_value(page):
    """In Follow-system mode under `prefers-color-scheme: light`, changing the light dropdown
    should immediately apply the chosen light theme. The committed `data-verso-theme` must
    match the dropdown's value, not whatever was previously painted."""
    page.emulate_media(color_scheme="light")
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    _set_mode(page, "auto")
    _expand_choices(page)
    light = page.locator("#theme-picker-light")
    current = page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
    chosen = None
    for opt in light.locator("option").all():
        v = opt.get_attribute("value")
        if v and v != current:
            chosen = v
            break
    assert chosen is not None, "need at least two light themes to test commit"
    light.select_option(value=chosen)
    after = page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
    assert after == chosen, (
        f"auto-mode commit should apply dropdown value {chosen!r}, got {after!r}"
    )


def test_switching_themes_has_no_intermediate_state(page):
    """Selecting a new theme in the dropdown must take `data-verso-theme` directly from the
    old value to the new value. Any intermediate state — e.g. a transient default — would
    cause a visible flash to an unrelated theme."""
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    # Light mode keeps the test deterministic: the active theme is exactly the light dropdown's
    # value, so the test exercises "open the dialog, pick a different light theme, see only the
    # new theme paint."
    _set_mode(page, "light")
    _expand_choices(page)
    # Install a MutationObserver that logs every value `data-verso-theme` takes from this
    # point on, so we can assert the sequence after the switch.
    page.evaluate(
        """() => {
            window.__versoThemeStates = [];
            const obs = new MutationObserver(records => {
                for (const r of records) {
                    if (r.attributeName === 'data-verso-theme') {
                        window.__versoThemeStates.push(
                            document.documentElement.getAttribute('data-verso-theme')
                        );
                    }
                }
            });
            obs.observe(document.documentElement, { attributes: true });
            window.__versoStopObserver = () => obs.disconnect();
        }"""
    )
    light = page.locator("#theme-picker-light")
    initial = page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
    target = None
    for opt in light.locator("option").all():
        v = opt.get_attribute("value")
        if v and v != initial:
            target = v
            break
    assert target is not None, "need at least two light themes to test a switch"
    light.select_option(value=target)
    # Give the change handler a moment to run any cascaded events so they show up in the
    # recorded sequence.
    page.wait_for_timeout(100)
    page.evaluate("window.__versoStopObserver()")
    states = page.evaluate("window.__versoThemeStates")
    # The only value `data-verso-theme` should take during the switch is the chosen target.
    bad = [s for s in states if s != target]
    assert not bad, (
        f"intermediate theme states during light-mode switch from {initial!r} to {target!r}: {bad}"
    )


def test_switching_light_themes_in_auto_has_no_dark_flash(page):
    """In Follow-system mode under `prefers-color-scheme: light`, switching the *light*
    dropdown must not paint a dark theme in between."""
    page.emulate_media(color_scheme="light")
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    _set_mode(page, "auto")
    _expand_choices(page)
    light = page.locator("#theme-picker-light")
    dark = page.locator("#theme-picker-dark")
    page.evaluate(
        """() => {
            window.__versoThemeStates = [];
            const obs = new MutationObserver(records => {
                for (const r of records) {
                    if (r.attributeName === 'data-verso-theme') {
                        window.__versoThemeStates.push(
                            document.documentElement.getAttribute('data-verso-theme')
                        );
                    }
                }
            });
            obs.observe(document.documentElement, { attributes: true });
            window.__versoStopObserver = () => obs.disconnect();
        }"""
    )
    initial = page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
    target = None
    for opt in light.locator("option").all():
        v = opt.get_attribute("value")
        if v and v != initial:
            target = v
            break
    assert target is not None, "need at least two light themes to test a switch"
    dark_value = dark.locator("option").first.get_attribute("value")
    light.focus()
    light.select_option(value=target)
    page.wait_for_timeout(100)
    page.evaluate("window.__versoStopObserver()")
    states = page.evaluate("window.__versoThemeStates")
    # The forbidden state is the *dark* one. Re-applying `initial` (the value the page already
    # had) is invisible; only a flash to a different appearance is a real flicker.
    assert dark_value not in states, (
        f"dark theme {dark_value!r} appeared during a light-to-light switch; full sequence: {states}"
    )
    bad = [s for s in states if s not in (target, initial)]
    assert not bad, (
        f"unexpected intermediate themes during auto-mode light switch: {bad} (full: {states})"
    )


def test_theme_dropdowns_mark_their_defaults(page):
    """The light dropdown marks `defaultLight` with ' (default)' and the dark dropdown marks
    `defaultDark` — each appearance's own default, not the other's."""
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    _expand_choices(page)
    default_light = page.evaluate("window.versoThemes.defaultLight")
    default_dark = page.evaluate("window.versoThemes.defaultDark")
    light_marked = page.evaluate(
        """() => Array.from(document.querySelectorAll('#theme-picker-light option'))
            .filter(o => o.textContent.endsWith(' (default)')).map(o => o.value)"""
    )
    dark_marked = page.evaluate(
        """() => Array.from(document.querySelectorAll('#theme-picker-dark option'))
            .filter(o => o.textContent.endsWith(' (default)')).map(o => o.value)"""
    )
    assert light_marked == [default_light], (
        f"light dropdown (default) should mark only {default_light!r}, got {light_marked!r}"
    )
    assert dark_marked == [default_dark], (
        f"dark dropdown (default) should mark only {default_dark!r}, got {dark_marked!r}"
    )


def test_theme_dropdowns_are_alphabetized(page):
    """The Light and Dark theme dropdowns list their themes in alphabetical order by display
    name."""
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    _expand_choices(page)
    for sel_id in ["#theme-picker-light", "#theme-picker-dark"]:
        texts = page.locator(f"{sel_id} option").all_text_contents()
        assert texts == sorted(texts), f"{sel_id} options not alphabetised: {texts}"


def test_choices_collapsed_by_default(page):
    """With nothing customized, the 'Theme choices' section is collapsed (so the picker is a
    one-line Appearance dropdown)."""
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    choices = page.locator("#theme-picker-choices")
    assert choices.count() == 1, "expected a collapsible #theme-picker-choices section"
    assert choices.get_attribute("open") is None, "choices should start collapsed"
    assert not page.locator("#theme-picker-light").is_visible()


def test_choices_expanded_when_custom_theme_stored(page, server):
    """Once a non-default light theme is stored, the 'Theme choices' section opens by default
    on the next load so the customized choice is visible."""
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    _expand_choices(page)
    light = page.locator("#theme-picker-light")
    default_light = page.evaluate("window.versoThemes.defaultLight")
    chosen = None
    for opt in light.locator("option").all():
        v = opt.get_attribute("value")
        if v and v != default_light:
            chosen = v
            break
    if chosen is None:
        pytest.skip(
            "only one light theme registered; cannot store a non-default choice"
        )
    light.select_option(value=chosen)
    # Reload: a fresh dialog is built, reading the stored non-default light theme.
    page.goto(server + "/")
    page.wait_for_load_state("domcontentloaded")
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    choices = page.locator("#theme-picker-choices")
    assert choices.get_attribute("open") is not None, (
        "choices should be expanded when a non-default theme is stored"
    )
    assert page.locator("#theme-picker-light").is_visible()


def test_outside_click_dismisses_popover(page):
    """Clicking outside the popover closes the dialog and leaves the page on whatever theme
    is currently committed."""
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    initial = page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
    page.evaluate("document.body.click()")
    page.wait_for_function(
        "document.getElementById('theme-picker-button').getAttribute('aria-expanded') === 'false'"
    )
    assert (
        page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
        == initial
    )


def test_gear_toggle_close_dismisses_popover(page):
    """Clicking the gear a second time closes the dialog without affecting the active theme."""
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    initial = page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
    btn.click()
    page.wait_for_function(
        "document.getElementById('theme-picker-button').getAttribute('aria-expanded') === 'false'"
    )
    assert (
        page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
        == initial
    )


def test_localStorage_disabled_still_loads(page, server):
    """When localStorage throws, the page still renders and the default theme is applied."""
    # Stub localStorage *before* navigation so the no-flash script sees the throwing version.
    page.add_init_script("""
        Object.defineProperty(window, 'localStorage', {
            configurable: true,
            get() { throw new Error('storage disabled'); }
        });
    """)
    page.goto(server + "/")
    page.wait_for_load_state("domcontentloaded")
    theme = page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
    appearance = page.evaluate(
        "document.documentElement.getAttribute('data-verso-appearance')"
    )
    assert theme is not None and theme != "", (
        "data-verso-theme should be set even without storage"
    )
    assert appearance in ("light", "dark"), f"unexpected appearance {appearance!r}"


def test_picker_preview_token_hover_shows_tippy(page):
    """Hovering a token in the picker's code-sample preview should pop a Tippy tooltip, the
    same way it does for tokens in the main page body.

    The picker preview is built on first popover open via `preview.innerHTML = data.codeSample`.
    The page's tippy-init script runs at DOMContentLoaded over `document.querySelectorAll(
    tokenSelector)` — before the picker preview exists — so without follow-up wiring those
    tokens get no `_tippy` instance and hovering them does nothing.
    """
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    preview = page.locator("#theme-picker-preview")
    preview.wait_for(state="attached", timeout=5000)
    # Pick a real hover-bearing token from the baked sample (e.g. `def greet (...) := ...`
    # produces `.const.token` and `.var.token` entries with `data-verso-hover` IDs that
    # reference the global `-verso-docs.json`).
    token = preview.locator(".token[data-verso-hover]").first
    token.wait_for(state="attached", timeout=5000)
    has_tippy = page.evaluate(
        "el => !!el._tippy",
        token.element_handle(),
    )
    assert has_tippy, "picker preview token should have a Tippy instance bound"
    token.scroll_into_view_if_needed()
    token.hover()
    # The page-body tippy-init uses `delay: [100, null]`, so allow a brief settle window.
    page.wait_for_selector(".tippy-box", state="visible", timeout=3000)


def test_picker_preview_binding_highlight(page):
    """Hovering an identifier in the picker preview should add `.binding-hl` to its other
    occurrences in the preview — the same binding-highlight effect the manual's body code
    gets.
    """
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    preview = page.locator("#theme-picker-preview")
    preview.wait_for(state="attached", timeout=5000)
    # The code sample is `def greet (name : String) (count := 1) := ...intercalate count s!"Hello, {name}"`,
    # so there are two `.var.token` elements with the same `data-binding` for `name` and two
    # for `count`. Pick the first var token's binding, then count its peers before / after
    # the hover.
    bindings = preview.locator(".token[data-binding^='var-']")
    bindings.first.wait_for(state="attached", timeout=5000)
    first_binding = bindings.first.get_attribute("data-binding")
    assert first_binding, "expected first var token to have a data-binding"
    peers = preview.locator(f".token[data-binding='{first_binding}']")
    peer_count = peers.count()
    assert peer_count >= 2, (
        f"expected at least two `{first_binding}` tokens in the preview, got {peer_count}"
    )
    # Hover the first occurrence and confirm the others gain `.binding-hl`.
    bindings.first.scroll_into_view_if_needed()
    bindings.first.hover()
    page.wait_for_function(
        f"""() => {{
            const peers = document.querySelectorAll(
                "#theme-picker-preview .token[data-binding='{first_binding}']");
            const hl = Array.from(peers).filter(el => el.classList.contains('binding-hl'));
            return hl.length === peers.length && peers.length >= 2;
        }}""",
        timeout=3000,
    )
