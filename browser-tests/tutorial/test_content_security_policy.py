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

# The markers that the custom scripts in `TutorialExampleMain.lean` set, one for each of the
# tutorial's standard mechanisms and one for a script from a listed external origin.
MARKERS = [
    "tutorialExtraJs",
    "tutorialExtraJsFile",
    EXTERNAL_SCRIPT_MARKER,
]

BUILD_COMMAND = (
    "lake run versoMain test-projects/tutorial-test/TutorialExampleMain.lean"
)


# The origin from which `TutorialExampleMain.lean` loads `external-script.js` when it is built with
# `VERSO_TEST_EXTERNAL_SCRIPT_PORT` set to the tests' `--port`.
@pytest.fixture(scope="session")
def external_script_origin(request):
    return external_script_origin_for_port(request.config, BUILD_COMMAND)


# The front page lists the tutorials, and each tutorial page has highlighted code with hovers.
PAGES = {
    "front": "/",
    "tutorial": "/hashmap/",
    "literate tutorial": "/literate/",
}


@pytest.fixture(params=PAGES.keys())
def loaded_page(request, server: str, page: Page):
    page.goto(server + PAGES[request.param])
    page.wait_for_load_state("networkidle")
    return page


class TestContentSecurityPolicy:
    # The `page` fixture fails the test if any of the page's own scripts is blocked.
    def test_policy_precedes_scripts(self, loaded_page: Page):
        assert_policy_precedes_scripts(loaded_page)

    def test_custom_scripts_run(self, loaded_page: Page, external_script_origin):
        assert_policy_lists_origin(loaded_page, external_script_origin, BUILD_COMMAND)
        assert_markers_set(loaded_page, MARKERS)

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
