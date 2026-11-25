import contextlib
import json
import pytest
import random
import socket
import subprocess
import time
from pathlib import Path
from urllib.parse import urlsplit
from playwright.sync_api import Error as PlaywrightError, sync_playwright

# TODO: adjust default path to built site relative to this directory
DEFAULT_SITE_DIR = "../_out/html-multi"
REDIRECTS_JSON_PATH = DEFAULT_SITE_DIR + "/xref.json"


def find_free_port():
    """Find an available port by binding to port 0."""
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def wait_for_server(proc, port, timeout=30):
    """Wait until the server process accepts connections on the port."""
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if proc.poll() is not None:
            raise RuntimeError(f"the test server exited with code {proc.returncode}")
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=1):
                return
        except OSError:
            time.sleep(0.1)
    proc.terminate()
    raise RuntimeError(f"the test server did not accept connections within {timeout}s")


def load_redirects():
    """Load redirects from JSON file and return a list of (source, target) tuples."""
    json_path = Path(__file__).parent / REDIRECTS_JSON_PATH
    with open(json_path) as f:
        data = json.load(f)

    sections = data["Verso.Genre.Manual.section"]["contents"]
    return [
        (s, sections[s][0]["address"] + "#" + sections[s][0]["id"]) for s in sections
    ]


def get_sample_redirects(n=10):
    """Get a random sample of n redirects for testing."""
    redirects = load_redirects()
    if len(redirects) <= n:
        return redirects
    return random.sample(redirects, n)


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


def pytest_configure(config):
    """Set random seed if provided."""
    seed = config.getoption("--seed")
    if seed is not None:
        random.seed(seed)


def pytest_generate_tests(metafunc):
    """Generate test cases for each sampled redirect."""
    if "redirect_case" in metafunc.fixturenames:
        n = metafunc.config.getoption("--num-redirects")
        redirects = get_sample_redirects(n)
        # Create readable test IDs
        ids = [f"{source}->{target}" for source, target in redirects]
        metafunc.parametrize("redirect_case", redirects, ids=ids)


@pytest.fixture(scope="session")
def server(request):
    """Start a local HTTP server for the built site, or use an existing one."""
    external_url = request.config.getoption("--server-url")

    if external_url:
        yield external_url
        return

    site_dir = request.config.getoption("--site-dir")
    site_dir = Path(__file__).parent / site_dir
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
    wait_for_server(proc, port)
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


def _origin(url):
    parts = urlsplit(url)
    return (parts.scheme, parts.netloc)


@pytest.fixture
def missing_file_allowlist():
    """URL paths of the site that may be missing without failing a test.

    A `conftest.py` in a test directory overrides this fixture for sites that have known gaps.
    """
    return []


# Reports each `securitypolicyviolation` event of every document in the page to the binding.
VIOLATION_LISTENER = """
document.addEventListener("securitypolicyviolation", (event) => {
  window.__versoReportContentSecurityPolicyViolation({
    blockedURI: event.blockedURI,
    violatedDirective: event.violatedDirective,
    effectiveDirective: event.effectiveDirective,
    sourceFile: event.sourceFile,
    lineNumber: event.lineNumber,
    columnNumber: event.columnNumber,
    sample: event.sample,
    documentURI: event.documentURI,
  });
}, true);
"""


def _is_about_content_security_policy(text):
    text = text.lower()
    return "content security policy" in text or "content-security-policy" in text


def describe_violation(violation):
    location = violation.get("sourceFile") or violation.get("documentURI") or "?"
    line = violation.get("lineNumber")
    column = violation.get("columnNumber")
    if line:
        location += f":{line}:{column}"
    blocked = violation.get("blockedURI") or "?"
    directive = violation.get("violatedDirective") or violation.get(
        "effectiveDirective"
    )
    text = f"blocked {blocked} by {directive} at {location}"
    if violation.get("sample"):
        text += f" (sample: {violation['sample']!r})"
    return text


# Console messages about the policy quote it in full, which can run to many kilobytes.
def describe_console_message(message, limit=400):
    if len(message) <= limit:
        return message
    return message[:limit] + f"... ({len(message) - limit} more characters)"


class ContentSecurityPolicyViolations:
    def __init__(self):
        self.violations = []
        self.console_messages = []
        self._page = None

    def attach(self, page):
        self._page = page
        page.expose_binding(
            "__versoReportContentSecurityPolicyViolation",
            lambda _source, violation: self.violations.append(violation),
        )
        page.add_init_script(VIOLATION_LISTENER)
        page.on("console", self._on_console)

    def detach(self):
        self._page.remove_listener("console", self._on_console)

    def _on_console(self, message):
        if _is_about_content_security_policy(message.text):
            self.console_messages.append(f"{message.type}: {message.text}")

    # Lets the page dispatch the violation events that it has queued. A page that has closed
    # or crashed has nothing left to dispatch.
    def settle(self):
        with contextlib.suppress(PlaywrightError):
            self._page.evaluate(
                "() => new Promise((resolve) => setTimeout(resolve, 0))"
            )

    def assert_clean(self):
        self.settle()
        failure = self.failure_message()
        assert failure is None, failure

    def expect_blocked_script(self, uri):
        # Cross-origin violation reports may omit the path of the blocked resource.
        url = urlsplit(uri)
        allowed_uris = {uri}
        if url.netloc:
            allowed_uris.add(f"{url.scheme}://{url.netloc}")

        def matches(event):
            return (
                event["blockedURI"] in allowed_uris
                and event["effectiveDirective"] in {"script-src", "script-src-elem"}
                and event["documentURI"].split("#")[0] == self._page.url.split("#")[0]
            )

        deadline = time.monotonic() + 5
        while not any(map(matches, self.violations)) and time.monotonic() < deadline:
            self._page.wait_for_timeout(50)
        self.settle()
        event = next((v for v in self.violations if matches(v)), None)
        assert event is not None, self.failure_message() or f"No blocked script for {uri}"
        self.violations.remove(event)

        # Chromium and Firefox also log the violation. Match the operation in the
        # diagnostic, excluding the policy text (which can mention unrelated URLs).
        for index, message in enumerate(self.console_messages):
            operation = message.lower().split(" violates ")[0].split(" because ")[0]
            if uri == "inline":
                expected = "inline script" in operation
            else:
                expected = uri.lower() in operation and "script" in operation
            if expected:
                self.console_messages.pop(index)
                break

    def failure_message(self):
        if not self.violations and not self.console_messages:
            return None
        lines = ["content security policy violations:"]
        lines += [f"  {describe_violation(v)}" for v in self.violations]
        if self.console_messages:
            lines.append("console messages about the content security policy:")
            lines += [f"  {describe_console_message(m)}" for m in self.console_messages]
        return "\n".join(lines)


@pytest.fixture
def content_security_policy_violations():
    return ContentSecurityPolicyViolations()


@pytest.fixture
def page(browser, request, missing_file_allowlist, content_security_policy_violations):
    """A fresh page that fails its test if the site's own files are missing or fail to load.

    Only HTTP errors and network failures for the site, the origin of the first navigation, count.
    Requests that the browser cancels itself, such as those that a navigation replaces, and the
    browser's favicon probe are ignored.
    Paths in `missing_file_allowlist` and tests that carry the `allow_missing_files` marker are
    exempt.
    """
    page = browser.new_page()
    content_security_policy_violations.attach(page)
    failures = []
    site = []

    def on_request(req):
        # The site is the origin of the page's first navigation.
        if not site and req.is_navigation_request() and req.frame == page.main_frame:
            if urlsplit(req.url).scheme in ("http", "https"):
                site.append(_origin(req.url))

    def counts(url):
        path = urlsplit(url).path
        return (
            bool(site)
            and _origin(url) == site[0]
            and path != "/favicon.ico"
            and path not in missing_file_allowlist
        )

    def on_response(response):
        if response.status >= 400 and counts(response.url):
            failures.append(f"{response.status} {response.url}")

    def on_request_failed(req):
        reason = req.failure or ""
        # Browsers name a request that they cancel themselves differently (ERR_ABORTED,
        # NS_BINDING_ABORTED, NS_ERROR_ABORT). A document whose load another navigation
        # replaces fails with a generic error in Firefox, so failures of navigations are
        # not counted; their HTTP errors are.
        cancelled = "ABORT" in reason.upper() or req.is_navigation_request()
        if not cancelled and counts(req.url):
            failures.append(f"failed ({reason}) {req.url}")

    page.on("request", on_request)
    page.on("response", on_response)
    page.on("requestfailed", on_request_failed)
    yield page
    content_security_policy_violations.settle()
    content_security_policy_violations.detach()
    page.remove_listener("request", on_request)
    page.remove_listener("response", on_response)
    page.remove_listener("requestfailed", on_request_failed)
    page.close()
    messages = []
    if failures and request.node.get_closest_marker("allow_missing_files") is None:
        messages.append(
            "requests for missing or unloadable files:\n" + "\n".join(failures)
        )
    violations = content_security_policy_violations.failure_message()
    if violations:
        messages.append(violations)
    if messages:
        pytest.fail("\n".join(messages), pytrace=False)
