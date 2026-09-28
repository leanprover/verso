"""
Cancelling runs, leaving and returning to a test, editing and saving its file, and restarting the
Lean server.
"""

import pytest
from playwright.sync_api import expect

from widget import (
    AWAIT,
    Widget,
    expect_exact_text,
    wait_for_html,
    wait_for_ticks,
    wait_until,
)

pytestmark = pytest.mark.errata_widget

# A test whose module takes several seconds to build, so that a run can be cancelled while it builds.
SLOW_BUILD = """\
/-- A test in a module that is slow to build. -/
@[test]
def scratch : Test := IO.println "built and ran"

run_elab IO.sleep 8000
"""

# A test in a module whose last line is a comment that the tests edit.
EDITABLE = """\
/-- A test in a module that the tests edit. -/
@[test]
def scratch : Test := IO.println "ran"

-- A comment to edit.
"""

# A test that writes a line every half second for a minute, in a module that the tests edit.
LONG_EDITABLE = """\
/-- A long test in a module that the tests edit. -/
@[test]
def scratch : Test := do
  for tick in [0:120] do
    IO.println s!"tick {tick}"
    IO.sleep 500
"""


def wait_for_no_runner(editor, decl):
    """Waits until no test runner runs the test `decl`."""
    wait_until(lambda: not editor.runner_processes(decl), timeout_ms=10_000)
    assert not editor.runner_processes(decl), f"a runner of {decl} is still running"


def return_to(editor, widget, module, decl, away):
    """
    Moves the cursor to `away` and back to `decl`, and waits until the widget that is shown again has
    the server's reply to its first question about the test.
    """
    editor.move_to(module, away)
    expect(widget.title).to_contain_text(away)
    mark = editor.relay.mark()
    editor.move_to(module, decl)
    expect(widget.title).to_contain_text(decl)
    editor.relay.wait_for_reply(AWAIT, decl=decl, after=mark)


def test_a_run_can_be_cancelled_while_it_builds(editor):
    editor.write_scratch(SLOW_BUILD)
    editor.show("Scratch", "scratch")
    widget = Widget(editor.page)
    widget.run_button.click()
    expect(widget.text("Building…")).to_be_visible()
    expect(widget.cancel_button).to_be_enabled()
    widget.cancel_button.click()
    expect(widget.text("cancelled")).to_be_visible()
    expect(widget.run_button).to_have_text("Run again")
    # The cancelled run stays with the server, ended and with no outcome of its own.
    report = editor.server_run("Scratch", "scratch")
    assert report["done"] and report.get("outcome") is None, report
    # The build of a later run starts over, and the run goes through.
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "built and ran\n")


def test_a_run_can_be_cancelled_while_it_runs(editor):
    editor.show("Passing", "slow")
    widget = Widget(editor.page)
    widget.run_button.click()
    wait_for_ticks(widget.output, 1)
    widget.cancel_button.click()
    expect(widget.text("cancelled")).to_be_visible()
    # The cancelled run stays with the server, ended and holding the output it had, and its runner
    # has exited.
    report = editor.server_run("Passing", "slow")
    assert report["done"] and report.get("outcome") is None, report
    assert report["chunks"], report
    wait_for_no_runner(editor, "slow")
    # A later run starts from its own beginning.
    widget.run_button.click()
    expect(widget.text("Running…")).to_be_visible()
    wait_for_ticks(widget.output, 2)


def test_returning_to_a_running_test_follows_it_without_repeating_output(editor):
    editor.show("Passing", "slow")
    widget = Widget(editor.page)
    widget.run_button.click()
    before = wait_for_ticks(widget.output, 2)
    return_to(editor, widget, "Passing", "slow", away="bothStreams")
    expect(widget.text("Running…")).to_be_visible()
    # The output shown again goes on from where the run is, each line once.
    wait_for_ticks(widget.output, len(before) + 4)
    expect(widget.verdict("Passed")).to_have_count(0)


def test_returning_to_a_finished_test_shows_its_result_as_it_was(editor):
    editor.show("Passing", "strayOutput")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect(widget.output).to_contain_text("stray output")
    shown = widget.root.inner_html()
    return_to(editor, widget, "Passing", "strayOutput", away="bothStreams")
    wait_for_html(widget.root, shown)


def test_a_result_is_kept_after_the_server_forgets_the_run(editor):
    editor.show("Passing", "copyOrder")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    shown = widget.root.inner_html()
    editor.move_to("Passing", "bothStreams")
    expect(widget.title).to_contain_text("bothStreams")
    # A server that has started again holds no runs, so it has nothing to report about this one.
    editor.restart_server()
    report = editor.server_run("Passing", "copyOrder")
    assert report["startTime"] == 0 and report.get("outcome") is None, report
    return_to(editor, widget, "Passing", "copyOrder", away="bothStreams")
    wait_for_html(widget.root, shown)


def test_cancelling_a_run_that_has_finished_leaves_its_result(editor):
    editor.show("Passing", "bothStreams")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    props = editor.widget_props("Passing", "bothStreams")
    reply = editor.call_rpc(
        "Passing", "bothStreams", "Errata.Widget.cancelTest", {"decl": props["decl"]}
    )
    # The run had finished, so the cancel had nothing to end and the outcome is still there.
    assert reply == {"cancelled": False}, reply
    report = editor.server_run("Passing", "bothStreams")
    assert report["outcome"] is not None, report
    expect(widget.verdict("Passed")).to_be_visible()


def test_editing_a_running_test_ends_its_run_wherever_the_cursor_is(editor):
    editor.write_scratch(LONG_EDITABLE)
    editor.show("Scratch", "scratch")
    widget = Widget(editor.page)
    widget.run_button.click()
    wait_for_ticks(widget.output, 1)
    assert editor.runner_processes("scratch")
    # With the cursor on another test, the widget for this one is gone when the test is edited.
    editor.move_to("Passing", "bothStreams")
    expect(widget.title).to_contain_text("bothStreams")
    text = editor.documents["Scratch"]["text"]
    editor.edit("Scratch", text.replace('s!"tick {tick}"', 's!"tock {tick}"'))
    wait_for_no_runner(editor, "scratch")


def test_unsaved_changes_block_a_run_and_a_saved_change_marks_the_result(editor):
    editor.write_scratch(EDITABLE)
    editor.show("Scratch", "scratch")
    widget = Widget(editor.page)
    text = editor.documents["Scratch"]["text"]
    editor.edit("Scratch", text.replace("A comment to edit.", "An edited comment."))
    expect(widget.text("unsaved — save to run")).to_be_visible()
    expect(widget.run_button).to_be_disabled()
    editor.save("Scratch")
    expect(widget.text("unsaved — save to run")).to_have_count(0)
    expect(widget.run_button).to_be_enabled()
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect(widget.text("File modified")).to_have_count(0)
    text = editor.documents["Scratch"]["text"]
    editor.edit(
        "Scratch", text.replace("An edited comment.", "A comment edited twice.")
    )
    expect(widget.text("File modified")).to_be_visible()
    expect(widget.text("— save to run")).to_be_visible()
    editor.save("Scratch")
    expect(widget.text("— save to run")).to_have_count(0)
    expect(widget.text("File modified")).to_be_visible()
    expect(widget.run_button).to_be_enabled()


def test_the_widget_reconnects_after_the_server_restarts(editor):
    editor.show("Passing", "bothStreams")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    editor.restart_server()
    expect(widget.title).to_contain_text("bothStreams")
    expect(widget.verdict("Passed")).to_be_visible()
    widget.run_button.click()
    expect(widget.text("Building…").or_(widget.text("Running…"))).to_be_visible()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "on stdout\non stderr\nstdout again\n")


def test_a_restart_notice_while_the_run_goes_on_repeats_no_output(editor):
    editor.show("Passing", "slow")
    widget = Widget(editor.page)
    widget.run_button.click()
    shown = wait_for_ticks(widget.output, 2)
    # The InfoView hears of a server restart while the same server keeps the run going, and the
    # widget asks for the run's output from the start again.
    editor.page.evaluate(
        "(result) => window.harness.serverRestarted(result)", editor.initialize_result
    )
    wait_for_ticks(widget.output, len(shown) + 4)
