"""The tests that share the Lean server at once, and the test modules that keep them apart."""

import json
import re

import pytest

from harness import Editor, LspRelay, RemoteLeanSession, TestModules, scratch_key
from widget import Widget, expect_exact_text

pytestmark = pytest.mark.errata_widget

# A test in a module whose elaboration also leaves a message naming its client.
CLIENT_SCRATCH = """\
/-- A test that names its client, with a pause so that both clients' runs are under way at once. -/
@[test]
def scratch : Test := do
  IO.println "from the {client} client"
  IO.sleep 3000

#eval "a message from the {client} client"
"""


def record_messages(session):
    """The list of the messages that the session's connection receives from now on."""
    seen = []
    forward = session.lean.on_message

    def on_message(message):
        """Records a message and passes it on."""
        seen.append(message)
        forward(message)

    session.lean.on_message = on_message
    return seen


def diagnostics(messages):
    """The URIs and the texts of the diagnostics among `messages`."""
    uris = set()
    texts = []
    for message in messages:
        if message.get("method") == "textDocument/publishDiagnostics":
            uris.add(message["params"]["uri"])
            texts.extend(d["message"] for d in message["params"]["diagnostics"])
    return uris, "\n".join(texts)


def test_two_clients_of_one_host_see_only_their_own_documents_and_runs(
    request, browser, editor, lean_host
):
    """
    Two clients of one host each run the test of their own scratch module at once. Each receives the
    diagnostics of its own module alone, and each module's run reports its own output and run.
    """
    page = browser.new_page()
    relay = LspRelay()
    session = RemoteLeanSession(lean_host)
    modules = TestModules(scratch_key(request.node.nodeid + "[second]"))
    other = Editor(page, relay, session, modules)
    try:
        other.start()
        assert modules.scratch != editor.modules.scratch
        assert modules.lane != editor.modules.lane
        seen_first = record_messages(editor.session)
        seen_second = record_messages(session)
        editor.write_scratch(CLIENT_SCRATCH.replace("{client}", "first"))
        other.write_scratch(CLIENT_SCRATCH.replace("{client}", "second"))
        editor.show("Scratch", "scratch")
        other.show("Scratch", "scratch")
        first = Widget(editor.page)
        second = Widget(page)
        first.run_button.click()
        second.run_button.click()
        first.wait_for_verdict("Passed")
        second.wait_for_verdict("Passed")
        expect_exact_text(first.output, "from the first client\n")
        expect_exact_text(second.output, "from the second client\n")
        uris, text = diagnostics(seen_first)
        assert uris == {editor.path("Scratch").as_uri()}, uris
        assert "first client" in text and "second client" not in text, text
        uris, text = diagnostics(seen_second)
        assert uris == {other.path("Scratch").as_uri()}, uris
        assert "second client" in text and "first client" not in text, text
        first_run = editor.server_run("Scratch", "scratch")
        second_run = other.server_run("Scratch", "scratch")
        assert first_run["runId"] != second_run["runId"]
        assert "first client" in json.dumps(first_run["chunks"])
        assert "second client" not in json.dumps(first_run["chunks"])
        assert "second client" in json.dumps(second_run["chunks"])
        assert "first client" not in json.dumps(second_run["chunks"])
    finally:
        other.close()
        modules.release()
        session.stop()
        relay.close()
        page.close()


def test_each_test_has_a_scratch_module_of_its_own_until_it_ends(request, test_modules):
    """
    A test's scratch module is named for the test, two tests' scratch modules and lanes differ, and a
    test's scratch module is gone once the test ends.
    """
    assert test_modules.scratch == "Scratch_" + scratch_key(request.node.nodeid)
    first = TestModules(scratch_key(request.node.nodeid + "[first]"))
    second = TestModules(scratch_key(request.node.nodeid + "[second]"))
    try:
        names = {test_modules.scratch, first.scratch, second.scratch}
        assert len(names) == 3, names
        for name in names:
            assert re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name), name
        assert len({test_modules.lane, first.lane, second.lane}) == 3
        first.write_scratch("-- A module with nothing in it.\n")
        assert first.path("Scratch").is_file()
        assert first.module_name("Scratch") in first.module_names()
    finally:
        first.release()
        second.release()
    assert not first.path("Scratch").exists()
