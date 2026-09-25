"""A Lean server that dies during a test, and the test that follows it."""

import time

import pytest

from harness import LspError, kill_trees
from widget import Widget

pytestmark = pytest.mark.errata_widget


def test_requests_to_a_server_that_died_fail_at_once(editor):
    """
    Once the Lean server has died, the page's requests and the harness's own end in an error within
    seconds, rather than when their timeouts run out.
    """
    editor.show("Passing", "streamed")
    uri = editor.path("Passing").as_uri()
    kill_trees([editor.lean.pid])
    start = time.monotonic()
    with pytest.raises(LspError):
        editor.lean.request(
            "textDocument/hover",
            {"textDocument": {"uri": uri}, "position": {"line": 0, "character": 0}},
            timeout=110,
        )
    # A request from the page, which the relay passes to the server. The page collects what the
    # relay delivers, so the test watches the deliveries themselves.
    delivered = []
    deliver = editor.relay._deliver

    def watch(message):
        delivered.append(message)
        deliver(message)

    editor.relay._deliver = watch
    editor.relay._from_page(
        {
            "jsonrpc": "2.0",
            "id": "after-the-server-died",
            "method": "textDocument/hover",
            "params": {"textDocument": {"uri": uri}, "position": {"line": 0, "character": 0}},
        }
    )

    def answered():
        return any(m.get("id") == "after-the-server-died" and "error" in m for m in delivered)

    while not answered():
        assert time.monotonic() - start < 10, "the page's request was not answered in 10 s"
        time.sleep(0.1)


def test_the_test_after_a_server_died_finds_one_running(editor):
    """The test after one whose Lean server died runs a test from the widget as usual."""
    editor.show("Passing", "streamed")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
