"""
Replies that arrive late or not at all. The relay holds or rejects particular calls, so each test
arranges an order of events that a person could only hit by chance.
"""

import pytest
from playwright.sync_api import expect

from widget import AWAIT, CANCEL, Widget, expect_exact_text, wait_for_ticks

pytestmark = pytest.mark.errata_widget


def test_a_cancel_reply_that_arrives_after_a_new_run_leaves_that_run_alone(editor):
    editor.show("Passing", "slow")
    widget = Widget(editor.page)
    widget.run_button.click()
    wait_for_ticks(widget.output, 1)
    late_cancel = editor.relay.hold_replies(CANCEL)
    widget.cancel_button.click()
    # The server ends the run, and the widget learns of it from its next report.
    late_cancel.wait_until_matched()
    expect(widget.text("cancelled")).to_be_visible()
    widget.run_button.click()
    wait_for_ticks(widget.output, 1)
    late_cancel.release()
    editor.relay.wait_for_reply(CANCEL)
    # The new run goes on as before, and its output keeps arriving.
    shown = wait_for_ticks(widget.output, 1)
    wait_for_ticks(widget.output, len(shown) + 3)
    expect(widget.text("Running…")).to_be_visible()
    expect(widget.text("cancelled")).to_have_count(0)


def test_a_cancel_that_arrives_after_the_test_finished_keeps_the_result(editor):
    editor.show("Passing", "bothStreams")
    widget = Widget(editor.page)
    slow_cancel = editor.relay.hold_requests(CANCEL)
    widget.run_button.click()
    expect(widget.cancel_button).to_be_enabled()
    widget.cancel_button.click()
    slow_cancel.wait_until_matched()
    # The cancel has yet to reach the server, so the test runs to the end.
    widget.wait_for_verdict("Passed")
    slow_cancel.release()
    editor.relay.wait_for_reply(CANCEL)
    editor.page.wait_for_timeout(500)
    expect(widget.verdict("Passed")).to_be_visible()
    expect(widget.text("cancelled")).to_have_count(0)
    expect_exact_text(widget.output, "on stdout\non stderr\nstdout again\n")


def test_rejected_reports_are_asked_for_again(editor):
    editor.show("Passing", "slow")
    widget = Widget(editor.page)
    # The widget first asks whether a run is already going, and there is none.
    editor.relay.wait_for_reply(AWAIT)
    widget.run_button.click()
    shown = wait_for_ticks(widget.output, 1)
    rejected = editor.relay.reject_requests(AWAIT, count=3)
    rejected.wait_until_matched()
    # After the rejections, the widget follows the run again, each line once.
    wait_for_ticks(widget.output, len(shown) + 6)
    assert rejected.remaining == 0
    expect(widget.text("Running…")).to_be_visible()


def test_a_run_whose_reports_keep_failing_can_still_be_cancelled_and_is_followed_again(
    editor,
):
    editor.show("Passing", "slow")
    widget = Widget(editor.page)
    editor.relay.wait_for_reply(AWAIT)
    widget.run_button.click()
    shown = wait_for_ticks(widget.output, 1)
    rejected = editor.relay.reject_requests(AWAIT, count=1_000)
    # The widget names the error and keeps the run's Cancel button while it keeps asking.
    expect(widget.text("reconnecting: rejected by the test harness")).to_be_visible()
    expect(widget.cancel_button).to_be_enabled()
    rejected.stop()
    # Once the reports come through again, the widget follows the run from where it left off.
    wait_for_ticks(widget.output, len(shown) + 4)
    expect(widget.text("reconnecting:")).to_have_count(0)
    widget.cancel_button.click()
    expect(widget.text("cancelled")).to_be_visible()


def test_a_rejected_cancel_is_tried_again(editor):
    editor.show("Passing", "slow")
    widget = Widget(editor.page)
    widget.run_button.click()
    wait_for_ticks(widget.output, 1)
    rejected = editor.relay.reject_requests(CANCEL, count=2)
    widget.cancel_button.click()
    expect(widget.text("cancelled")).to_be_visible()
    assert rejected.remaining == 0
    expect(widget.text("could not cancel")).to_have_count(0)


def test_a_cancel_that_reaches_the_server_after_a_new_run_leaves_that_run_alone(editor):
    editor.show("Passing", "streamed")
    widget = Widget(editor.page)
    widget.run_button.click()
    expect(widget.output).to_contain_text("step 1", timeout=120_000)
    late_cancel = editor.relay.hold_requests(CANCEL)
    widget.cancel_button.click()
    late_cancel.wait_until_matched()
    # The cancel has yet to reach the server, so the run ends on its own, and the next one starts.
    widget.wait_for_verdict("Passed")
    widget.run_button.click()
    expect(widget.output).to_contain_text("step 1", timeout=120_000)
    late_cancel.release()
    editor.relay.wait_for_reply(CANCEL)
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "step 1\nstep 2\nstep 3\nstep 4\n")
