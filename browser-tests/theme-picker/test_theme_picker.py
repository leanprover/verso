"""
Browser tests for the theme picker (gear button + popover + dropdowns).

Builds the user's guide (which ships multiple themes via @[manual_theme]) and exercises:
  * gear placement in header-tools, left of the search box
  * popover open/close, role + aria-* attributes, Escape returns focus to the gear
  * focus trap inside the popover
  * theme switching via dropdown sets data-verso-theme and data-verso-appearance
  * persistence across reloads via localStorage
  * "match system" auto-mode follows matchMedia(prefers-color-scheme), single mode does not
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


def test_theme_switching_persists(page, server):
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    # Force single mode (the toggle starts on auto/checked when the picker has both
    # light and dark themes; unchecking it switches to single).
    mode = page.locator("#theme-picker-mode")
    if mode.is_checked():
        mode.uncheck()
    # Pick the second option in the single dropdown.
    single = page.locator("#theme-picker-single")
    options = single.locator("option").all_text_contents()
    if len(options) < 2:
        pytest.skip("not enough themes registered to test switching")
    chosen = single.locator("option").nth(1).get_attribute("value")
    single.select_option(value=chosen)
    # The data attribute should reflect the choice immediately.
    assert (
        page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
        == chosen
    )
    # localStorage persists it.
    assert page.evaluate("localStorage.getItem('verso-theme-single')") == chosen
    # Reload: the no-flash script reads localStorage and applies the same theme before paint.
    page.goto(server + "/")
    page.wait_for_load_state("domcontentloaded")
    assert (
        page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
        == chosen
    )


def test_match_system_follows_media(page):
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    mode = page.locator("#theme-picker-mode")
    if not mode.is_checked():
        mode.check()
    # Emulate dark, then light; the inline script's matchMedia listener should swap themes.
    page.emulate_media(color_scheme="dark")
    page.wait_for_timeout(50)
    dark_id = page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
    page.emulate_media(color_scheme="light")
    page.wait_for_timeout(50)
    light_id = page.evaluate(
        "document.documentElement.getAttribute('data-verso-theme')"
    )
    assert dark_id != light_id, (
        "auto mode should pick different themes for light vs dark"
    )


def test_single_mode_ignores_media(page):
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    mode = page.locator("#theme-picker-mode")
    if mode.is_checked():
        mode.uncheck()
    # Pick a specific theme.
    chosen = page.locator("#theme-picker-single option").nth(0).get_attribute("value")
    page.locator("#theme-picker-single").select_option(value=chosen)
    # Emulating a media change must not override the chosen theme.
    page.emulate_media(color_scheme="dark")
    page.wait_for_timeout(50)
    assert (
        page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
        == chosen
    )
    page.emulate_media(color_scheme="light")
    page.wait_for_timeout(50)
    assert (
        page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
        == chosen
    )


def test_auto_commit_applies_dropdown_value(page):
    """In auto mode, changing the light dropdown while `prefers-color-scheme: light` is active
    should immediately apply the chosen light theme. The committed `data-verso-theme` must
    match the dropdown's value, not whatever was previously painted."""
    page.emulate_media(color_scheme="light")
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    mode = page.locator("#theme-picker-mode")
    if not mode.is_checked():
        mode.check()
    # Find a light-appearance option that differs from the currently visible theme.
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
    # The select-change handler fires `commit()`, which must apply the dropdown's value.
    after = page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
    assert after == chosen, (
        f"auto-mode commit should apply dropdown value {chosen!r}, got {after!r}"
    )


def test_switching_themes_has_no_intermediate_state(page):
    """Selecting a new theme in the dropdown must take `data-verso-theme` directly from the
    old value to the new value. Any intermediate state — e.g. a hover/focus preview on the
    *other* mode's dropdown firing during the click, or a transient default — would cause a
    visible flash to an unrelated theme."""
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    # Single mode keeps the test deterministic: only one dropdown is visible, so the test
    # exercises the user path of "open the dialog, pick a different theme, see only the new
    # theme paint."
    mode = page.locator("#theme-picker-mode")
    if mode.is_checked():
        mode.uncheck()
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
    single = page.locator("#theme-picker-single")
    initial = page.evaluate("document.documentElement.getAttribute('data-verso-theme')")
    target = None
    for opt in single.locator("option").all():
        v = opt.get_attribute("value")
        if v and v != initial:
            target = v
            break
    assert target is not None, "need at least two themes to test a switch"
    single.select_option(value=target)
    # Give the change handler a moment to run any cascaded events (focus/mouseenter previews,
    # outside-click handler, etc.) so they show up in the recorded sequence.
    page.wait_for_timeout(100)
    page.evaluate("window.__versoStopObserver()")
    states = page.evaluate("window.__versoThemeStates")
    # The only value `data-verso-theme` should take during the switch is the chosen target.
    # Any other id (e.g. PageTheme, defaultDark, etc.) means there was an intermediate paint.
    bad = [s for s in states if s != target]
    assert not bad, (
        f"intermediate theme states during single-mode switch from {initial!r} to {target!r}: {bad}"
    )


def test_switching_light_themes_in_auto_has_no_dark_flash(page):
    """In auto mode under `prefers-color-scheme: light`, switching the *light* dropdown must
    not paint a dark theme in between. The hover/focus preview handlers were attached to the
    dark dropdown too, so a stray mouseenter (Playwright's `select_option` walks the cursor
    over the dialog) could fire `previewTheme(darkSel.value)` mid-switch."""
    page.emulate_media(color_scheme="light")
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    mode = page.locator("#theme-picker-mode")
    if not mode.is_checked():
        mode.check()
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
    # Real-user flow: focus the light dropdown (as a normal user would click on it) and
    # pick a new option. Hovering the *other* dropdown is also part of the picked-up bug,
    # but a previous version fired the dark preview because a stray mouseenter on the dark
    # dropdown landed during Playwright's option-click; both paths should land on the
    # target theme and only on the target theme.
    light.focus()
    light.select_option(value=target)
    page.wait_for_timeout(100)
    page.evaluate("window.__versoStopObserver()")
    states = page.evaluate("window.__versoThemeStates")
    # The forbidden state is the *dark* one. Re-applying `initial` (the value the page
    # already had when the test snapshotted it) is invisible to the user; only a flash to
    # a different appearance, or to a third unrelated theme, is a real flicker.
    assert dark_value not in states, (
        f"dark theme {dark_value!r} appeared during a light-to-light switch; full sequence: {states}"
    )
    bad = [s for s in states if s not in (target, initial)]
    assert not bad, (
        f"unexpected intermediate themes during auto-mode light switch: {bad} (full: {states})"
    )


def test_single_mode_marks_single_default(page):
    """The single-mode dropdown marks `data.defaultSingle` with " (default)", not the light
    default unconditionally. Authors who set `defaultSingleAppearance := .dark` should see
    the dark theme labelled as the default in single mode."""
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    mode = page.locator("#theme-picker-mode")
    if mode.is_checked():
        mode.uncheck()
    single_default_id = page.evaluate("window.versoThemes.defaultSingle")
    # The option text for the single-default id is the only one with " (default)" appended.
    marked = page.evaluate(
        """(id) => {
            const opts = Array.from(document.querySelectorAll('#theme-picker-single option'));
            return opts
                .filter(o => o.textContent.endsWith(' (default)'))
                .map(o => o.value);
        }""",
        single_default_id,
    )
    assert marked == [single_default_id], (
        f"single-mode (default) should mark only {single_default_id!r}, got {marked!r}"
    )


def test_themes_are_alphabetized(page):
    """Every dropdown lists its themes in alphabetical order by display name."""
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    mode = page.locator("#theme-picker-mode")
    for sel_id, ensure_auto in [
        ("#theme-picker-single", False),
        ("#theme-picker-light", True),
        ("#theme-picker-dark", True),
    ]:
        if ensure_auto and not mode.is_checked():
            mode.check()
        if not ensure_auto and mode.is_checked():
            mode.uncheck()
        texts = page.locator(f"{sel_id} option").all_text_contents()
        assert texts == sorted(texts), f"{sel_id} options not alphabetised: {texts}"


def test_match_system_toggle_hides_rows(page):
    """The 'Theme' (single) row is visible only when Match system is OFF; Light and Dark are
    visible only when Match system is ON. The `[hidden]` attribute on the row elements must
    actually hide them — earlier CSS made the `.theme-picker-row { display: flex }` rule
    win over the default `[hidden] { display: none }`, so the toggle did nothing."""
    btn = _picker_button(page)
    btn.click()
    _dialog(page).wait_for(state="attached", timeout=5000)
    mode = page.locator("#theme-picker-mode")

    # Auto on -> Light + Dark visible, Theme hidden.
    if not mode.is_checked():
        mode.check()
    assert page.locator("#theme-picker-light").is_visible()
    assert page.locator("#theme-picker-dark").is_visible()
    assert not page.locator("#theme-picker-single").is_visible()

    # Auto off -> Theme visible, Light + Dark hidden.
    mode.uncheck()
    assert page.locator("#theme-picker-single").is_visible()
    assert not page.locator("#theme-picker-light").is_visible()
    assert not page.locator("#theme-picker-dark").is_visible()


def test_outside_click_dismisses_popover(page):
    """Clicking outside the popover closes the dialog and leaves the page on whatever theme
    is currently committed. (The picker commits on `change` and no longer has a hover/focus
    preview path, so dismissal is purely a "close the popover" action.)"""
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
    tokens get no `_tippy` instance and hovering them does nothing. This test currently fails
    and is the acceptance criterion for that fix.
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
    # The bug shows up two ways and the test asserts both. (1) The preview token has no
    # `_tippy` instance attached (the page-level tippy-init scanned the DOM before the
    # picker preview existed). (2) Hovering the token does not produce a `.tippy-box`.
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

    The per-`.hl.lean` mouseover handler is attached at DOMContentLoaded over
    `document.querySelectorAll('.hl.lean')`; the picker preview is built later, so without a
    follow-up `window.versoAttachBindingHighlights(...)` call the listener never fires and
    hovering one `name` leaves the other one untouched.
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
