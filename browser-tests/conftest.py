import json
import pytest
import random
import socket
import subprocess
import time
from pathlib import Path
from playwright.sync_api import sync_playwright

# The built site, relative to this directory, when neither the Errata setting `siteDir` nor
# `--site-dir` names another.
DEFAULT_SITE_DIR = "../_out/html-multi"

# The Errata settings that the browser tests take, when Verso's pytest harness runs them: the built
# site, which `errata.toml` binds per suite, and Errata's seed, from which the redirect tests draw.
errata_settings_decl = {
    "siteDir": {
        "description": "The directory of the built site that the tests serve; --site-dir otherwise."
    },
    "Errata.seed": {"description": "The seed that chooses the redirects to test."},
}


def find_free_port():
    """Find an available port by binding to port 0."""
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def wait_for_port(port, timeout=10.0):
    """Wait until a server accepts connections on the local port, for at most `timeout` seconds."""
    deadline = time.monotonic() + timeout
    while True:
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=0.5):
                return
        except OSError:
            if time.monotonic() > deadline:
                raise
            time.sleep(0.02)


def load_redirects(site_dir):
    """Load redirects from the site's JSON file and return a list of (source, target) tuples."""
    with open(Path(site_dir) / "xref.json") as f:
        data = json.load(f)

    sections = data["Verso.Genre.Manual.section"]["contents"]
    return [
        (s, sections[s][0]["address"] + "#" + sections[s][0]["id"]) for s in sections
    ]


def errata_settings_of(request):
    """
    The Errata settings that the test received from Verso's pytest harness, or an empty dictionary
    when pytest runs without the harness.
    """
    try:
        return request.getfixturevalue("errata_settings")
    except pytest.FixtureLookupError:
        return {}


def pytest_addoption(parser):
    parser.addoption(
        "--port",
        action="store",
        default=None,
        help="Port for the local test server (default: auto-select)",
    )
    parser.addoption(
        "--site-dir",
        action="store",
        default=DEFAULT_SITE_DIR,
        help="Path to the built site directory",
    )
    parser.addoption(
        "--server-url",
        action="store",
        default=None,
        help="Use an existing server instead of starting one (e.g., http://localhost:3000)",
    )
    parser.addoption(
        "--num-redirects",
        action="store",
        default=10,
        type=int,
        help="Number of random redirects to test (default: 10)",
    )
    parser.addoption(
        "--seed",
        action="store",
        default=None,
        type=int,
        help="Random seed for reproducible redirect selection",
    )


def pytest_generate_tests(metafunc):
    """Generate one test per redirect to check; each test draws its redirect when it runs."""
    if "redirect_index" in metafunc.fixturenames:
        n = metafunc.config.getoption("--num-redirects")
        metafunc.parametrize(
            "redirect_index", range(n), ids=[f"redirect-{i}" for i in range(n)]
        )


def pytest_collection_modifyitems(config, items):
    """
    Marks every browser test with `browser`, the tag that Errata's default filter leaves out, and
    marks the tests that serve a site or draw redirects as taking the Errata settings they read.
    """
    for item in items:
        item.add_marker(pytest.mark.browser)
        if "site_dir" in item.fixturenames:
            item.add_marker(pytest.mark.errata_setting("siteDir", optional=True))
        if "redirect_case" in item.fixturenames:
            item.add_marker(pytest.mark.errata_setting("Errata.seed", optional=True))


@pytest.fixture(scope="session")
def site_dir(request):
    """The built site: the Errata setting `siteDir` when the test received it, and `--site-dir` otherwise."""
    site = errata_settings_of(request).get("siteDir") or request.config.getoption("--site-dir")
    return (Path(__file__).parent / site).resolve()


@pytest.fixture
def redirect_case(request, redirect_index, site_dir):
    """
    A redirect to check, as a (source, target) pair, drawn from the site's redirects with the Errata
    seed or `--seed` when either is given, so that a test with the same seed checks the same redirect.
    """
    seed = errata_settings_of(request).get("Errata.seed")
    if seed is None:
        seed = request.config.getoption("--seed")
    rng = random.Random(f"{seed}:{redirect_index}") if seed is not None else random.Random()
    return rng.choice(load_redirects(site_dir))


@pytest.fixture(scope="session")
def server(request, site_dir):
    """Start a local HTTP server for the built site, or use an existing one."""
    external_url = request.config.getoption("--server-url")

    if external_url:
        yield external_url
        return

    port = request.config.getoption("--port")

    if port is None:
        port = find_free_port()
    else:
        port = int(port)

    proc = subprocess.Popen(
        ["python", "-m", "http.server", str(port), "--bind", "127.0.0.1"],
        cwd=site_dir,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    wait_for_port(port)
    yield f"http://127.0.0.1:{port}"
    proc.terminate()
    proc.wait()


@pytest.fixture(scope="session")
def playwright_instance():
    with sync_playwright() as p:
        yield p


@pytest.fixture(scope="session", params=["chromium", "firefox"])
def browser(request, playwright_instance):
    """Parameterized fixture to run tests in multiple browsers."""
    browser_type = request.param
    browser = getattr(playwright_instance, browser_type).launch()
    yield browser
    browser.close()


@pytest.fixture
def page(browser):
    page = browser.new_page()
    yield page
    page.close()
