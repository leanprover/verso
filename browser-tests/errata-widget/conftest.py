"""
Fixtures for the Errata widget tests. Within a session, tests share one Lean server, and each test
gets a fresh page with the InfoView and an editor that connects the page to the server.
"""

import pytest
from playwright.sync_api import Page, expect

from harness import FIXTURE, INFOVIEW, Editor, LeanSession, LspRelay
from widget import EXPECT_TIMEOUT

# Playwright's own timeout for an assertion, which each widget test restores as it ends.
PLAYWRIGHT_EXPECT_TIMEOUT = 5_000


@pytest.fixture(autouse=True)
def expect_timeout():
    """
    Gives the assertions of the widget tests the time that a Lean server needs to answer. The
    timeout is Playwright's own global, so it is set for one test at a time and the tests of other
    suites in the same run keep the timeout they expect.
    """
    expect.set_options(timeout=EXPECT_TIMEOUT)
    yield
    expect.set_options(timeout=PLAYWRIGHT_EXPECT_TIMEOUT)


@pytest.fixture(scope="session")
def browser(playwright_instance):
    """The widget runs in the InfoView of VS Code, whose webviews are Chromium."""
    browser = playwright_instance.chromium.launch()
    yield browser
    browser.close()


@pytest.fixture(scope="session")
def fixture_workspace():
    """
    Checks that the InfoView is installed, and removes the fixture workspace's manifest so that Lake
    resolves the workspace against Verso's own dependencies.
    """
    if not INFOVIEW.is_dir():
        pytest.fail(
            "the InfoView is missing; run `npm ci` in the repository root first"
        )
    manifest = FIXTURE / "lake-manifest.json"
    if manifest.exists():
        manifest.unlink()


@pytest.fixture(scope="session")
def lean_session(fixture_workspace):
    session = LeanSession()
    yield session
    session.stop()


@pytest.fixture
def relay():
    relay = LspRelay()
    yield relay
    relay.close()


@pytest.hookimpl(wrapper=True)
def pytest_runtest_makereport(item, call):
    report = yield
    setattr(item, "report_" + report.when, report)
    return report


def print_diagnostics(page, console, session):
    """Prints what a reader needs to see why a test failed: the page, the browser, and the server."""
    try:
        print(
            "--- InfoView text ---\n"
            + page.locator("#infoview").inner_text(timeout=5_000)
        )
    except Exception as error:  # noqa: BLE001 - the diagnostics go on without the page's text
        print(f"--- InfoView text unavailable: {error}")
    print("--- browser console ---\n" + "\n".join(console))
    print("--- Lean server stderr ---\n" + session.lean.stderr_tail())


@pytest.fixture
def editor(request, page: Page, relay: LspRelay, lean_session: LeanSession):
    page.set_default_timeout(120_000)
    console = []
    page.on(
        "console", lambda message: console.append(f"{message.type}: {message.text}")
    )
    page.on("pageerror", lambda error: console.append(f"page error: {error}"))
    editor = Editor(page, relay, lean_session)
    try:
        editor.start()
    except BaseException:
        print_diagnostics(page, console, lean_session)
        editor.close()
        raise
    yield editor
    call = getattr(request.node, "report_call", None)
    if call is not None and call.failed:
        print_diagnostics(page, console, lean_session)
    editor.close()
