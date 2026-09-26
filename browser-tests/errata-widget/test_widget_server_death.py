"""A Lean server that dies during a test, and the one server that the host starts after it."""

import os
import threading
import time
from pathlib import Path

import pytest

from harness import LspError, RemoteLeanSession, descendants, matching

pytestmark = pytest.mark.errata_widget

# Where macOS writes a report for each crashed process, Python's fatal errors at exit among them.
CRASH_REPORTS = Path.home() / "Library" / "Logs" / "DiagnosticReports"

# A module whose elaboration takes a minute before its last declaration, so that a request about
# that declaration waits for the server's answer.
SLOW_TO_ELABORATE = """\
run_elab IO.sleep 60000

def later : Nat := 1
"""


def python_crash_reports():
    """The names of the Python processes' crash reports, or `None` where the directory is absent."""
    if not CRASH_REPORTS.is_dir():
        return None
    return {p.name for p in CRASH_REPORTS.glob("Python-*.ips")}


def server_processes(pid):
    """The Lean server processes at or below `pid`, the process that the host started."""
    return (matching(r"lean --server") - matching(r"--worker")) & ({pid} | set(descendants(pid)))


def alive(pid):
    """Whether a process with the id `pid` exists."""
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


@pytest.mark.lean_server_alone
def test_a_server_that_dies_fails_the_pending_requests_and_is_started_once_again(
    editor, lean_host
):
    """
    When the Lean server dies, a request that it has yet to answer and later requests from the page
    end in an error within seconds. Clients that then ask the host for a running server at once all
    receive the one new server, which answers the next request, and no Python process crashes on
    the way.
    """
    reports = python_crash_reports()
    editor.write_scratch(SLOW_TO_ELABORATE)
    editor.open("Scratch")
    uri = editor.path("Scratch").as_uri()
    lines = editor.documents["Scratch"]["text"].split("\n")
    position = {"line": lines.index("def later : Nat := 1"), "character": 4}
    outcome = {}

    def hover():
        """Asks for a hover that waits for the module's elaboration, and records how it ended."""
        try:
            editor.lean.request(
                "textDocument/hover",
                {"textDocument": {"uri": uri}, "position": position},
                timeout=110,
            )
            outcome["error"] = None
        except (LspError, TimeoutError) as error:
            outcome["error"] = error
        outcome["at"] = time.monotonic()

    pending = threading.Thread(target=hover)
    pending.start()
    time.sleep(2)
    old = editor.lean.pid
    servers = server_processes(old)
    assert servers, "no Lean server process was found"
    for pid in servers:
        os.kill(pid, 9)
    start = time.monotonic()
    pending.join(timeout=30)
    assert "at" in outcome, "the pending request was not answered in 30 s"
    assert isinstance(outcome["error"], LspError), outcome
    assert "exited" in str(outcome["error"]), outcome
    assert outcome["at"] - start < 10, "the pending request was not answered in 10 s"
    # A request from the page, which the relay passes to the server. The page collects what the
    # relay delivers, so the test watches the deliveries themselves.
    delivered = []
    deliver = editor.relay._deliver

    def watch(message):
        """Records a message that the relay delivers to the page, and delivers it."""
        delivered.append(message)
        deliver(message)

    editor.relay._deliver = watch
    editor.relay._from_page(
        {
            "jsonrpc": "2.0",
            "id": "after-the-server-died",
            "method": "textDocument/hover",
            "params": {"textDocument": {"uri": uri}, "position": position},
        }
    )

    def answered():
        """Whether the page's request has received an error reply."""
        return any(m.get("id") == "after-the-server-died" and "error" in m for m in delivered)

    while not answered():
        assert time.monotonic() - start < 10, "the page's request was not answered in 10 s"
        time.sleep(0.1)
    # Three clients ask the host for a running server at once.
    others = [RemoteLeanSession(lean_host) for _ in range(2)]
    try:
        pids = []

        def ensure(session):
            """Asks the host for a running server and records its process id."""
            session.initialize_result = session.lean.control("ensure")["initialize"]
            pids.append(session.lean.pid)

        asking = [threading.Thread(target=ensure, args=(s,)) for s in [editor.session, *others]]
        for thread in asking:
            thread.start()
        for thread in asking:
            thread.join(timeout=300)
        assert len(pids) == 3 and len(set(pids)) == 1, pids
        assert pids[0] != old and not alive(old), (old, pids)
    finally:
        for session in others:
            session.stop()
    editor.documents = {}
    editor.rpc_sessions = {}
    editor.open("Passing")
    assert editor.widget_props("Passing", "streamed")["decl"]
    if reports is not None:
        assert python_crash_reports() == reports, "a Python process crashed"
