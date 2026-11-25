import contextlib

import pytest
from playwright.sync_api import Page
from playwright.sync_api import TimeoutError as PlaywrightTimeoutError

# The marker that the fixture sites' `external-script.js` sets. The sites load that script from an
# external origin that their policies list as an extra script source.
EXTERNAL_SCRIPT_MARKER = "versoExternalScript"


# The external origin of a fixture site that the tests serve on `--port`. The `server` fixture serves
# the site from `127.0.0.1`, so `localhost` on the same port is a different origin to the browser
# that reaches the same files. The site must be built with `VERSO_TEST_EXTERNAL_SCRIPT_PORT` set to
# the same port.
def external_script_origin_for_port(config, build_command):
    port = config.getoption("--port")
    if port is None:
        pytest.fail(
            f"These tests need --port. Build the site with "
            f"VERSO_TEST_EXTERNAL_SCRIPT_PORT=PORT {build_command} "
            f"and pass the same PORT.",
            pytrace=False,
        )
    return f"http://localhost:{port}"


def assert_policy_lists_origin(page: Page, origin, build_command):
    policy = page.locator('meta[http-equiv="Content-Security-Policy"]').get_attribute(
        "content"
    )
    sources = policy.split(";")[0].split()
    assert origin in sources, (
        f"the content security policy doesn't list {origin}. Build the site with "
        f"VERSO_TEST_EXTERNAL_SCRIPT_PORT={origin.rsplit(':', 1)[1]} {build_command} and run the tests "
        f"with the same --port."
    )


# Counts the policies and lists the scripts and `<base>` elements that don't follow the first one.
# A browser ignores a `<meta>` policy for the scripts and `<base>` that come before it.
HEAD_ORDER = """
() => {
  const policies = document.querySelectorAll('meta[http-equiv="Content-Security-Policy" i]');
  const others = document.querySelectorAll("script, base");
  const policy = policies[0];
  return {
    policyCount: policies.length,
    inHead: policy !== undefined && policy.parentElement === document.head,
    notAfterPolicy: Array.from(others)
      .filter((e) => policy === undefined ||
        !(policy.compareDocumentPosition(e) & Node.DOCUMENT_POSITION_FOLLOWING))
      .map((e) => e.outerHTML.slice(0, 120)),
  };
}
"""


def assert_policy_precedes_scripts(page: Page):
    order = page.evaluate(HEAD_ORDER)
    assert order["policyCount"] == 1, (
        f"expected one policy, found {order['policyCount']}"
    )
    assert order["inHead"], "the policy is not a child of <head>"
    assert order["notAfterPolicy"] == [], (
        "these elements come before the policy: " + ", ".join(order["notAfterPolicy"])
    )


INJECT_INLINE_SCRIPT = """
() => {
  const script = document.createElement("script");
  script.textContent = "window.versoInjectedInlineScript = true;";
  document.head.append(script);
  return window.versoInjectedInlineScript === true;
}
"""


# A script that the page didn't ship has no hash in the policy, so the browser refuses to run it.
def assert_injected_inline_script_blocked(page: Page, violations):
    ran = page.evaluate(INJECT_INLINE_SCRIPT)
    assert not ran, "an injected inline script ran"
    reported = violations.wait_for(1)
    violations.take()
    assert reported, "the browser reported no violation for an injected inline script"
    directive = reported[0].get("effectiveDirective") or reported[0].get(
        "violatedDirective"
    )
    assert directive.startswith("script-src"), reported


INJECT_EXTERNAL_SCRIPT = """
(src) => new Promise((resolve) => {
  const script = document.createElement("script");
  script.src = src;
  script.onload = () => resolve("loaded");
  script.onerror = () => resolve("blocked");
  document.head.append(script);
})
"""


# A script from an origin that the policy doesn't list is blocked.
def assert_unlisted_origin_blocked(page: Page, violations, origin: str):
    assert (
        page.evaluate(
            INJECT_EXTERNAL_SCRIPT, f"{origin}/-verso-data/external-script.js"
        )
        == "blocked"
    )
    reported = violations.wait_for(1)
    violations.take()
    assert any(v.get("blockedURI", "").startswith(origin) for v in reported), reported


MISSING_MARKERS = "(markers) => markers.filter((m) => window[m] === undefined)"


# Scripts that load other scripts can finish after the page's load event, so this waits briefly.
def assert_markers_set(page: Page, markers, timeout=5000):
    with contextlib.suppress(PlaywrightTimeoutError):
        page.wait_for_function(
            f"(markers) => ({MISSING_MARKERS})(markers).length === 0",
            arg=markers,
            timeout=timeout,
        )
    missing = page.evaluate(MISSING_MARKERS, markers)
    assert missing == [], f"the scripts that set these markers didn't run: {missing}"
