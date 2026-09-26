"""
Fixtures for the Errata widget tests. The tests share one Lean server, which a host process serves
to any number of tests at once: under Verso's pytest harness, the host that the Errata fixture
`leanServer` starts for the run, and otherwise one that the pytest session starts. Each test gets a
fresh page with the InfoView, test modules of its own, and an editor that connects the page to the
server.
"""

import json
import subprocess
import sys
import time
from pathlib import Path

import pytest
from playwright.sync_api import Page, expect

import harness
import services
from harness import FIXTURE, INFOVIEW, Editor, LspRelay, RemoteLeanSession, TestModules
from harness import scratch_key, sweep_test_modules
from widget import EXPECT_TIMEOUT

# Playwright's own timeout for an assertion, which each widget test restores as it ends.
PLAYWRIGHT_EXPECT_TIMEOUT = 5_000


def check_fixture_workspace():
    """
    Checks that the InfoView is installed, removes the manifest of the widget's workspace so that
    Lake resolves the workspace against Verso's own dependencies, and removes the test modules that
    earlier tests left behind.
    """
    if not INFOVIEW.is_dir():
        raise RuntimeError("the InfoView is missing; run `npm ci` in the repository root first")
    manifest = FIXTURE / "lake-manifest.json"
    if manifest.exists():
        manifest.unlink()
    sweep_test_modules()


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


def lean_server_teardown(address, context):
    """
    The teardown of the fixture `leanServer`: it stops the host, the server, and their runs, and
    removes the test modules that tests left behind.
    """
    services.stop(context, "leanServer", group_first=False, grace=20.0)
    sweep_test_modules()


# The Lean server that the tests share. Each test opens documents in modules of its own and, when it
# ends, ends its runs and closes its documents; the host closes the documents that a connection
# still owns when the connection ends. The fixture has a setup and a teardown. The tests marked
# `lean_server_alone` claim it exclusive, and the others claim it shared. Every phase of the fixture
# and every test that uses it takes one slot of the pool, so as many widget tests run at once as the
# pool has slots. The host starts the server with `LEAN_NUM_THREADS` removed from its environment.
errata_fixtures_decl = {
    "leanServer": {
        "description": "A Lean server in the widget's fixture workspace, which the tests share.",
        "threads": 1,
        "setup": lean_server_setup,
        "teardown": lean_server_teardown,
    },
}


def start_local_host(directory):
    """
    Starts this suite's harness as the host of a Lean server for a pytest session without the Errata
    runner, and returns the host's process and address once the host is ready.
    """
    ready = directory / "ready.json"
    proc = subprocess.Popen([sys.executable, harness.__file__, "serve", str(ready)])
    deadline = time.monotonic() + 300
    while not ready.is_file():
        if proc.poll() is not None:
            raise RuntimeError("the host of the Lean server exited before it was ready")
        if time.monotonic() > deadline:
            proc.kill()
            raise RuntimeError("the host of the Lean server was not ready within 300 s")
        time.sleep(0.1)
    return proc, f"127.0.0.1:{json.loads(ready.read_text())['port']}"


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
def lean_host(request, tmp_path_factory):
    """
    The address of the host of the tests' Lean server: the host of the Errata fixture `leanServer`
    under Verso's pytest harness, and otherwise one that this session starts and stops.
    """
    address = errata_fixtures_of(request).get("leanServer")
    if address:
        yield address
        return
    try:
        check_fixture_workspace()
        proc, address = start_local_host(tmp_path_factory.mktemp("lean-host"))
    except RuntimeError as error:
        pytest.fail(str(error))
    yield address
    proc.terminate()
    proc.wait()
    sweep_test_modules()


@pytest.fixture(scope="session")
def lean_session(lean_host):
    """
    The pytest session's connection to the host of the Lean server, which the session's tests share
    and which ends when the session ends.
    """
    session = RemoteLeanSession(lean_host)
    yield session
    session.stop()


@pytest.fixture
def test_modules(request):
    """
    The test's own modules: its scratch module, named for its node id, and its lane. When the test
    ends, its scratch module is removed and its lane is free for another test.
    """
    modules = TestModules(scratch_key(request.node.nodeid))
    yield modules
    modules.release()


@pytest.fixture
def relay():
    """The relay between the test's page and the Lean server, closed when the test ends."""
    relay = LspRelay()
    yield relay
    relay.close()


def pytest_configure(config):
    """Registers the marker of the tests that use the Lean server alone."""
    config.addinivalue_line(
        "markers",
        "lean_server_alone: the test uses the widget's Lean server alone among its users, since it "
        "stops the server or changes what every run reads",
    )


def pytest_collection_modifyitems(config, items):
    """
    Marks the widget tests, which take several seconds each, `slow`, and marks the tests that use a
    Lean server or test modules as claims on the Errata fixture `leanServer`: exclusive for the
    tests marked `lean_server_alone`, and shared otherwise. The fixture's setup and teardown remove
    test modules, so they never overlap a test that holds some.
    """
    here = Path(__file__).parent
    for item in items:
        if here in Path(item.path).parents:
            item.add_marker(pytest.mark.slow)
            if {"lean_session", "lean_host", "test_modules"} & set(item.fixturenames):
                alone = item.get_closest_marker("lean_server_alone") is not None
                item.add_marker(pytest.mark.errata_fixture("leanServer", exclusive=alone))


@pytest.hookimpl(wrapper=True)
def pytest_runtest_makereport(item, call):
    """Keeps each phase's report on the test item, where the `editor` fixture reads it."""
    report = yield
    setattr(item, "report_" + report.when, report)
    return report


def print_diagnostics(page, console, session):
    """Prints what shows why a test failed: the page's text, the browser console, and the server."""
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
def editor(
    request,
    page: Page,
    relay: LspRelay,
    lean_session: RemoteLeanSession,
    test_modules: TestModules,
):
    """
    The test's editor, started on its page, relay, and modules, and closed when the test ends; a
    failed start or a failed test prints the diagnostics.
    """
    page.set_default_timeout(120_000)
    console = []
    page.on(
        "console", lambda message: console.append(f"{message.type}: {message.text}")
    )
    page.on("pageerror", lambda error: console.append(f"page error: {error}"))
    editor = Editor(page, relay, lean_session, test_modules)
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
