import pytest
from content_security_policy_checks import (
    EXTERNAL_SCRIPT_MARKER,
    assert_injected_inline_script_blocked,
    assert_markers_set,
    assert_policy_lists_origin,
    assert_policy_precedes_scripts,
    assert_unlisted_origin_blocked,
    external_script_origin_for_port,
)
from playwright.sync_api import Page

# The markers that the custom scripts in `PackageManualMain.lean` set. Each script is added
# through one of the manual's standard mechanisms, and several have bodies that the browser
# normalizes or that the printer escapes before hashing. A script whose hash doesn't match the
# policy is blocked, and the `page` fixture reports the violation.
MARKERS = [
    "packageManualExtraJs",
    "packageManualCrLf",
    "packageManualLoneCr",
    "packageManualNul",
    "packageManualNonAscii",
    "packageManualExtraJsFile",
    "packageManualExtraHead",
    "packageManualEscapedText",
    "packageManualHtmlComment",
    "packageManualSvgText",
    "packageManualForeignObjectText",
    EXTERNAL_SCRIPT_MARKER,
]

BUILD_COMMAND = "lake run versoMain test-projects/package-manual/PackageManualMain.lean --output _out/package-manual"


# The origin from which `PackageManualMain.lean` loads `external-script.js` when it is built with
# `VERSO_TEST_EXTERNAL_SCRIPT_PORT` set to the tests' `--port`.
@pytest.fixture(scope="session")
def external_script_origin(request):
    return external_script_origin_for_port(request.config, BUILD_COMMAND)


PAGES = {
    "front": "/",
    "content": "/Documentation-Features/",
    "search": "/search/?q=zipper",
    "find": "/find/?domain=Verso.Genre.Manual.section&name=no-such-name",
}


@pytest.fixture(params=PAGES.keys())
def loaded_page(request, server: str, page: Page):
    page.goto(server + PAGES[request.param])
    page.wait_for_load_state("networkidle")
    return page


class TestContentSecurityPolicy:
    def test_policy_precedes_scripts(self, loaded_page: Page):
        assert_policy_precedes_scripts(loaded_page)

    def test_custom_scripts_run(self, loaded_page: Page, external_script_origin):
        assert_policy_lists_origin(loaded_page, external_script_origin, BUILD_COMMAND)
        assert_markers_set(loaded_page, MARKERS)

    # The printer escapes the text node, and the browser runs the escaped text.
    def test_escaped_text_reaches_the_browser(self, loaded_page: Page):
        assert (
            loaded_page.evaluate("window.packageManualEscapedText")
            == "a &amp;&amp; b &lt; c"
        )

    # In SVG, the browser decodes the printer's escapes before it runs the script.
    def test_svg_script_text_is_decoded(self, loaded_page: Page):
        assert loaded_page.evaluate("window.packageManualSvgText") == "a && b < c"
        assert loaded_page.evaluate("window.packageManualSvgRaw") == "a < b &amp;&"

    # In an SVG `foreignObject`, the browser runs the escaped text, as in HTML.
    def test_foreign_object_script_text_is_escaped(self, loaded_page: Page):
        assert (
            loaded_page.evaluate("window.packageManualForeignObjectText")
            == "a &amp;&amp; b"
        )

    # The NUL in the string literal arrives as U+FFFD, which is also what the policy hashes.
    def test_nul_becomes_replacement_character(self, loaded_page: Page):
        assert loaded_page.evaluate("window.packageManualNul") == "a�b"

    def test_injected_inline_script_is_blocked(
        self, loaded_page: Page, content_security_policy_violations
    ):
        assert_injected_inline_script_blocked(
            loaded_page, content_security_policy_violations
        )

    # `127.0.0.2` is a loopback address that the policy doesn't list. The browser checks the
    # policy before it connects, so the script is blocked whether or not a server answers there.
    def test_unlisted_origin_is_blocked(
        self,
        loaded_page: Page,
        content_security_policy_violations,
        external_script_origin,
    ):
        assert_unlisted_origin_blocked(
            loaded_page,
            content_security_policy_violations,
            external_script_origin.replace("localhost", "127.0.0.2"),
        )
