"""
The configuration of a small pytest suite that the conformance suite runs through Verso's pytest
harness. It declares the suite's Errata settings and fixtures, a pytest fixture whose setup fails,
and the suite's own marker. The Errata fixtures show the ways a fixture's phases can end, as those
of the conformance suite's shell scripts do.
"""

import os
import sys
import tempfile
import time

import pytest

# The Errata settings that the suite's tests and fixtures take: a greeting with a default, a
# setting without one, and a file that the users of `stamped` stamp.
errata_settings_decl = {
    "greeting": {"description": "A greeting.", "default": "hello"},
    "needed": {"description": "A setting without a default."},
    "stamp-file": {"description": "A file that users stamp."},
}


def stamp(path, line):
    """Appends a line to a file, when a file is given."""
    if path:
        with open(path, "a", encoding="utf-8") as f:
            f.write(line + "\n")


def stamped_setup(context):
    """Stamps the file, and gives it as the value."""
    path = context.settings.get("stamp-file", "")
    stamp(path, "setup")
    return path


def stamped_prepare(value, context):
    """Stamps the file as the prepare starts and, a moment later, as it ends."""
    stamp(value, "prepare start")
    time.sleep(0.1)
    stamp(value, "prepare end")


def fail_on_request(what):
    """A phase that fails with an assertion."""

    def phase(*_):
        """Fails with an assertion that names the phase."""
        raise AssertionError(f"the {what} failed on request")

    return phase


def report_teardown(value, context):
    """Prints whether the teardown received a value."""
    print(f"teardown received {value if value is not None else 'no value'}")


def prepare_fails_once(value, context):
    """Fails the first time it runs, noting that in the value's directory."""
    mark = os.path.join(value, "failed-once")
    if not os.path.exists(mark):
        open(mark, "w").close()
        raise AssertionError("the prepare failed on request")


def slow_setup(context):
    """Sleeps past any short timeout."""
    print("setting up", flush=True)
    time.sleep(30)
    return "slept"


def threaded_setup(context):
    """Prints the thread grant and LEAN_NUM_THREADS, and gives the grant as the value."""
    print(f"threads: {context.threads}; LEAN_NUM_THREADS: {os.environ.get('LEAN_NUM_THREADS', '')}")
    return str(context.threads)


# The Errata fixtures that the suite's tests use.
errata_fixtures_decl = {
    "stamped": {
        "description": "Its value is the stamp file.",
        "settings": [{"name": "stamp-file", "optional": True}],
        "setup": stamped_setup,
        "prepare": stamped_prepare,
        "teardown": lambda value, context: stamp(value, "teardown"),
    },
    "setup-fails": {
        "description": "Its setup fails.",
        "setup": fail_on_request("setup"),
        "teardown": report_teardown,
    },
    "prepare-fails": {
        "description": "Its first prepare fails.",
        "setup": lambda context: tempfile.mkdtemp(),
        "prepare": prepare_fails_once,
    },
    "teardown-fails": {
        "description": "Its teardown fails.",
        "setup": lambda context: "ready",
        "teardown": fail_on_request("teardown"),
    },
    "dependent": {
        "description": "It joins a greeting and another fixture's value.",
        "settings": ["greeting"],
        "fixtures": ["stamped"],
        "setup": lambda c: f"{c.settings['greeting']} and {c.fixtures['stamped']}",
    },
    "slow-setup": {
        "description": "Its setup sleeps.",
        "setup": slow_setup,
        "teardown": report_teardown,
    },
    "threaded": {
        "description": "It asks for threads.",
        "threads": 3,
        "setup": threaded_setup,
    },
    "calls-pytest-fail": {
        "description": "Its setup calls pytest.fail.",
        "setup": lambda context: pytest.fail("the setup gave up"),
        "teardown": report_teardown,
    },
    "calls-exit": {
        "description": "Its setup calls sys.exit.",
        "setup": lambda context: sys.exit(3),
        "teardown": report_teardown,
    },
}


def pytest_configure(config):
    """Registers the suite's marker."""
    config.addinivalue_line("markers", "chatty: a test that talks")


@pytest.fixture
def broken():
    """A fixture whose setup fails."""
    raise RuntimeError("the fixture broke")
