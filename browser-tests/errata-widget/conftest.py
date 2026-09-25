"""
Fixtures for the Errata widget tests. The tests share one Lean server: under Verso's pytest harness,
the server that the Errata fixture `leanServer` hosts for the run, and otherwise one that the pytest
session starts. Each test gets a fresh page with the InfoView and an editor that connects the page
to the server.
"""

import json
import sys
from pathlib import Path

import pytest
from playwright.sync_api import Page, expect

import harness
import services
from harness import FIXTURE, INFOVIEW, Editor, LeanSession, LspRelay, RemoteLeanServer
from harness import RemoteLeanSession
from widget import EXPECT_TIMEOUT

# Playwright's own timeout for an assertion, which each widget test restores as it ends.
PLAYWRIGHT_EXPECT_TIMEOUT = 5_000


def check_fixture_workspace():
    """
    Checks that the InfoView is installed, and removes the manifest of the widget's workspace so
    that Lake resolves the workspace against Verso's own dependencies.
    """
    if not INFOVIEW.is_dir():
        raise RuntimeError("the InfoView is missing; run `npm ci` in the repository root first")
    manifest = FIXTURE / "lake-manifest.json"
    if manifest.exists():
        manifest.unlink()


def lean_server_setup(context):
    """
    The setup of the fixture `leanServer`, which starts this suite's harness as the host of a Lean
    server and returns the host's address.
    """
    check_fixture_workspace()
    ready = services.state_dir(context, "leanServer") / "ready.json"
    proc = services.start(
        context, "leanServer", [sys.executable, harness.__file__, "serve", str(ready)],
        watches_lifeline=True,
    )

    def port():
        """The port that the host has written to its ready file, or `None` before it has."""
        try:
            return json.loads(ready.read_text())["port"]
        except (OSError, ValueError, KeyError):
            return None

    found = services.wait_until(port, 300, "the Lean server", proc, context, "leanServer")
    return f"127.0.0.1:{found}"


def lean_server_prepare(address, context):
    """
    The prepare of the fixture `leanServer`, which readies the server for the next test: it ends the
    runs that the server's file workers started and closes the documents that earlier tests left
    open, or starts a new server when the last one has exited.
    """
    lean = RemoteLeanServer(address, lambda message: None)
    try:
        lean.control("reset")
    finally:
        lean.close()


def lean_server_teardown(address, context):
    """The teardown of the fixture `leanServer`: it stops the host, the server, and their runs."""
    services.stop(context, "leanServer", group_first=False, grace=20.0)


# The Lean server that the tests share. Each test uses it alone among its users, since the tests
# open documents in one workspace and write its scratch module. Its phases ask for the threads of
# the server's workers and the builds they start, which run under the grant of the phase that
# started the server.
errata_fixtures_decl = {
    "leanServer": {
        "description": "A Lean server in the widget's fixture workspace, which the tests share.",
        "threads": 4,
        "setup": lean_server_setup,
        "prepare": lean_server_prepare,
        "teardown": lean_server_teardown,
    },
}


def errata_fixtures_of(request):
    """
    The values of the Errata fixtures that the test received from Verso's pytest harness, or an
    empty dictionary when pytest runs without the harness.
    """
    try:
        return request.getfixturevalue("errata_fixtures")
    except pytest.FixtureLookupError:
        return {}


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
def browser(request, playwright_instance):
    """
    The widget runs in the InfoView of VS Code, whose webviews are Chromium: a connection to the
    server of the Errata fixture `chromium` under Verso's pytest harness, and otherwise a browser
    that this process launches.
    """
    endpoint = errata_fixtures_of(request).get("chromium")
    chromium = playwright_instance.chromium
    browser = chromium.connect(endpoint) if endpoint else chromium.launch()
    yield browser
    browser.close()


@pytest.fixture(scope="session")
def lean_session(request):
    """
    The Lean server of the tests: the server of the Errata fixture `leanServer` under Verso's pytest
    harness, and otherwise one that this session starts.
    """
    address = errata_fixtures_of(request).get("leanServer")
    if address:
        session = RemoteLeanSession(address)
    else:
        try:
            check_fixture_workspace()
        except RuntimeError as error:
            pytest.fail(str(error))
        session = LeanSession()
    yield session
    session.stop()


@pytest.fixture
def relay():
    """The relay between the test's page and the Lean server, closed when the test ends."""
    relay = LspRelay()
    yield relay
    relay.close()


def pytest_collection_modifyitems(config, items):
    """
    Marks the widget tests `slow`, since each takes several seconds, and marks the tests that use a
    Lean server as using the Errata fixture `leanServer`.
    """
    here = Path(__file__).parent
    for item in items:
        if here in Path(item.path).parents:
            item.add_marker(pytest.mark.slow)
            if "lean_session" in item.fixturenames:
                item.add_marker(pytest.mark.errata_fixture("leanServer"))


@pytest.hookimpl(wrapper=True)
def pytest_runtest_makereport(item, call):
    """Keeps each phase's report on the test item, where the `editor` fixture reads it."""
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
    """
    The test's editor, started on its page and relay, and closed when the test ends; a failed start
    or a failed test prints the diagnostics.
    """
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
