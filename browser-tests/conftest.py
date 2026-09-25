import fcntl
import json
import os
import random
import shutil
import subprocess
import sys
from contextlib import contextmanager
from pathlib import Path

import pytest
from playwright.sync_api import sync_playwright

import services

# The repository's root, where the Errata runner starts the browser suites.
REPO = Path(__file__).resolve().parent.parent

# The built site, relative to this directory, when pytest runs outside Verso's pytest harness and
# `--site-dir` names no other.
DEFAULT_SITE_DIR = "../_out/html-multi"

# The variables that Lake sets for the processes it starts, which a Lake of another workspace must
# not inherit.
LAKE_VARS = (
    "LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP", "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH",
    "LEAN_SRC_PATH", "LEAN_GITHASH", "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH",
)

# The sites that the browser suites test, by the name that a suite's `--errata-site` gives. A site
# is either the value of a setting, which `errata.toml` binds to a Lake target of the root, or the
# output of a build in a test project, with the settings that bind the root's executables that the
# build runs.
SITES = {
    "usersguide": {"setting": "usersGuideSite"},
    "package-manual": {"setting": "packageManualSite"},
    "literate": {
        "project": "test-projects/literate-config",
        "settings": ["versoLiterateExe", "versoLiterateHtmlExe", "versoLiteratePlanExe"],
    },
    "literate-multi-root": {
        "project": "test-projects/literate-multi-root",
        "settings": ["versoLiterateExe", "versoLiterateHtmlExe", "versoLiteratePlanExe"],
    },
    "verso-html": {
        "project": "test-projects/literate-config",
        "target": "+LitConfig:literate",
        "settings": ["versoLiterateExe", "versoHtmlExe"],
    },
}

# The browsers that the tests run in, each an Errata fixture of the same name.
BROWSERS = ("chromium", "firefox")

# The Errata settings that the browser tests and their fixtures take, when Verso's pytest harness
# runs them: the sites and the executables that the site fixtures need, and Errata's seed, from
# which the redirect tests draw.
errata_settings_decl = {
    "usersGuideSite": {"description": "The built multi-page HTML of the user's guide."},
    "packageManualSite": {
        "description": "The built multi-page HTML of the package manual example."
    },
    "versoLiterateExe": {"description": "The built `verso-literate` executable."},
    "versoLiterateHtmlExe": {"description": "The built `verso-literate-html` executable."},
    "versoLiteratePlanExe": {"description": "The built `verso-literate-plan` executable."},
    "versoHtmlExe": {"description": "The built `verso-html` executable."},
    "Errata.seed": {"description": "The seed that chooses the redirects to test."},
}

# The Errata fixtures of the suite, which `pytest_configure` fills in: a browser server per
# browser, and for a suite with a site, the site and an HTTP server that serves it.
errata_fixtures_decl = {}


def wait_for_port(port, timeout=10.0):
    """Wait until a server accepts connections on the local port, for at most `timeout` seconds."""
    services.wait_until(lambda: True if services.accepts(port) else None, timeout,
                        f"the server on port {port}")


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


def errata_fixtures_of(request):
    """
    The values of the Errata fixtures that the test received from Verso's pytest harness, or an
    empty dictionary when pytest runs without the harness.
    """
    try:
        return request.getfixturevalue("errata_fixtures")
    except pytest.FixtureLookupError:
        return {}


@contextmanager
def project_lock(project):
    """
    Holds the build lock of a test project, the file `.lake/errata-build.lock` there, which every
    fixture that builds the project locks, the literate tests' fixture among them.
    """
    lake = REPO / project / ".lake"
    lake.mkdir(parents=True, exist_ok=True)
    with open(lake / "errata-build.lock", "a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def lake(project, *args, capture=False):
    """
    Runs Lake in a test project, without the variables of the Lake that started the run, and fails
    with Lake's output when it fails. Returns Lake's standard output when `capture` is true.
    """
    env = {k: v for k, v in os.environ.items() if k not in LAKE_VARS}
    result = subprocess.run(
        ["lake", *args], cwd=REPO / project, env=env, text=True,
        stdout=subprocess.PIPE if capture else sys.stderr, stderr=sys.stderr,
    )
    if result.returncode != 0:
        command = " ".join(args)
        raise RuntimeError(f"`lake {command}` in {project} failed with code {result.returncode}")
    return result.stdout if capture else None


def site_setup(site):
    """The setup of the fixture `site` for a site of `SITES`, which returns the site's directory."""

    def setup(context):
        if "setting" in site:
            return str((REPO / context.settings[site["setting"]]).resolve())
        project = site["project"]
        with project_lock(project):
            print(f"Building the site of {project}...", flush=True)
            # The manifest follows Verso's, whose clones of the dependencies the project shares.
            lake(project, "update", "verso")
            if "target" not in site:
                out = lake(project, "query", ":literateHtml", capture=True)
                return out.strip().splitlines()[-1]
            lake(project, "build", site["target"])
            literate = REPO / project / ".lake" / "build" / "literate"
            out = REPO / ".lake" / "build" / "sites" / "verso-html"
            shutil.rmtree(out, ignore_errors=True)
            subprocess.run(
                [context.settings["versoHtmlExe"], str(literate), str(out)],
                cwd=REPO, check=True, stdout=sys.stderr,
            )
            return str(out)

    return setup


def server_setup(context):
    """The setup of the fixture `server`: it serves the site on a free port and returns the URL."""
    port = services.free_port()
    proc = services.start(
        context, "server",
        [sys.executable, "-m", "http.server", str(port), "--bind", "127.0.0.1",
         "--directory", context.fixtures["site"]],
    )
    services.wait_until(lambda: True if services.accepts(port) else None, 30,
                        "the site's HTTP server", proc, context, "server")
    return f"http://127.0.0.1:{port}"


def browser_setup(name):
    """
    The setup of a browser's fixture, which starts Playwright's server for the browser and returns
    the server's WebSocket endpoint, to which each test connects.
    """

    def setup(context):
        state = services.state_dir(context, name)
        state.mkdir(parents=True, exist_ok=True)
        config = state / "launch.json"
        config.write_text(json.dumps({"headless": True}))
        proc = services.start(
            context, name,
            [sys.executable, "-m", "playwright", "launch-server", "--browser", name,
             "--config", str(config)],
        )

        def endpoint():
            for line in services.log_of(context, name).splitlines():
                if line.startswith("ws://"):
                    return line.strip()
            return None

        return services.wait_until(endpoint, 60, f"Playwright's {name} server", proc, context, name)

    return setup


def service_teardown(name):
    """The teardown of a fixture whose setup starts a service, which stops the service."""

    def teardown(value, context):
        services.stop(context, name)

    return teardown


def fixture_declarations(site_name):
    """
    The Errata fixtures of a suite whose site is `site_name` from `SITES`, or of a suite without a
    site when it is `None`. None of them has a prepare: each test opens a browser context of its own
    on its own connection to the browser, and reads the site without changing it.
    """
    decl = {}
    for name in BROWSERS:
        decl[name] = {
            "description": f"Playwright's {name} server, which each test connects to.",
            "setup": browser_setup(name),
            "teardown": service_teardown(name),
        }
    if site_name is not None:
        site = SITES[site_name]
        settings = [site["setting"]] if "setting" in site else site["settings"]
        decl["site"] = {
            "description": f"The built site {site_name}.",
            "settings": settings,
            "setup": site_setup(site),
        }
        decl["server"] = {
            "description": f"An HTTP server for the site {site_name}.",
            "fixtures": ["site"],
            "setup": server_setup,
            "teardown": service_teardown("server"),
        }
    return decl


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
        default=None,
        help=f"Path to the built site directory (default: {DEFAULT_SITE_DIR}, or the site that the "
        "Errata fixture `site` builds under Verso's pytest harness)",
    )
    parser.addoption(
        "--errata-site",
        action="store",
        default=None,
        choices=sorted(SITES),
        help="The site that the suite tests, which Errata fixtures build and serve under Verso's "
        "pytest harness",
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


def pytest_configure(config):
    """Declares the Errata fixtures of the suite, which depend on the suite's site."""
    errata_fixtures_decl.clear()
    errata_fixtures_decl.update(fixture_declarations(config.getoption("--errata-site")))


def pytest_generate_tests(metafunc):
    """Generate one test per redirect to check; each test draws its redirect when it runs."""
    if "redirect_index" in metafunc.fixturenames:
        n = metafunc.config.getoption("--num-redirects")
        metafunc.parametrize(
            "redirect_index", range(n), ids=[f"redirect-{i}" for i in range(n)]
        )


def pytest_collection_modifyitems(config, items):
    """
    Marks every browser test with `browser`, the tag that the default profile's filter in
    `errata.toml` leaves out, and marks each test as using the Errata fixtures that it reaches
    through pytest's fixtures: the server of the browser it runs in, and the suite's site and HTTP
    server. Tests share these fixtures: each connects to the browser with a context of its own, and
    reads the site through the server. Tests that draw redirects also take the seed.
    """
    has_site = config.getoption("--errata-site") is not None
    for item in items:
        item.add_marker(pytest.mark.browser)
        if "browser" in item.fixturenames:
            callspec = getattr(item, "callspec", None)
            name = callspec.params.get("browser", "chromium") if callspec else "chromium"
            item.add_marker(pytest.mark.errata_fixture(name, exclusive=False))
        if has_site and "site_dir" in item.fixturenames:
            item.add_marker(pytest.mark.errata_fixture("site", exclusive=False))
        if has_site and "server" in item.fixturenames:
            item.add_marker(pytest.mark.errata_fixture("server", exclusive=False))
        if "redirect_case" in item.fixturenames:
            item.add_marker(pytest.mark.errata_setting("Errata.seed", optional=True))


@pytest.fixture(scope="session")
def site_dir(request):
    """
    The built site: `--site-dir` when the command line gives it, and otherwise the value of the
    Errata fixture `site` under Verso's pytest harness, or the default site outside the harness.
    """
    site = request.config.getoption("--site-dir")
    if site is None:
        site = errata_fixtures_of(request).get("site", DEFAULT_SITE_DIR)
    return (Path(__file__).parent / site).resolve()


@pytest.fixture
def redirect_case(request, redirect_index, site_dir):
    """
    A redirect to check, as a (source, target) pair, drawn from the site's redirects with the
    setting `Errata.seed` or `--seed` when either is given, so that a test with the same seed checks
    the same redirect.
    """
    seed = errata_settings_of(request).get("Errata.seed")
    if seed is None:
        seed = request.config.getoption("--seed")
    rng = random.Random(f"{seed}:{redirect_index}") if seed is not None else random.Random()
    return rng.choice(load_redirects(site_dir))


@pytest.fixture(scope="session")
def server(request):
    """
    The URL of an HTTP server for the built site: `--server-url` when the command line gives it,
    the value of the Errata fixture `server` under Verso's pytest harness, and otherwise a local
    server that this fixture starts.
    """
    external_url = request.config.getoption("--server-url")
    if external_url:
        yield external_url
        return

    shared = errata_fixtures_of(request).get("server")
    if shared:
        yield shared
        return

    port = request.config.getoption("--port")
    port = services.free_port() if port is None else int(port)
    proc = subprocess.Popen(
        ["python", "-m", "http.server", str(port), "--bind", "127.0.0.1"],
        cwd=request.getfixturevalue("site_dir"),
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


def connect_or_launch(request, playwright_instance, name):
    """
    A browser of the named kind: a connection to the server of the Errata fixture of that name under
    Verso's pytest harness, and otherwise a browser that this process launches.
    """
    browser_type = getattr(playwright_instance, name)
    endpoint = errata_fixtures_of(request).get(name)
    return browser_type.connect(endpoint) if endpoint else browser_type.launch()


@pytest.fixture(scope="session", params=BROWSERS)
def browser(request, playwright_instance):
    """Parameterized fixture to run tests in multiple browsers."""
    browser = connect_or_launch(request, playwright_instance, request.param)
    yield browser
    browser.close()


@pytest.fixture
def page(browser):
    page = browser.new_page()
    yield page
    page.close()
