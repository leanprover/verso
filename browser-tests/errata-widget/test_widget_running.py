"""Running a test from the widget, and what the widget shows of the run and its output."""

import re

import pytest
from playwright.sync_api import expect

from harness import matching
from widget import AWAIT, RUN_TIMEOUT, Widget, expect_exact_text, wait_until

pytestmark = pytest.mark.errata_widget


def test_status_goes_from_building_to_running_to_a_verdict(editor):
    editor.show("Passing", "streamed")
    widget = Widget(editor.page)
    # The widget first asks whether a run is already going, and there is none.
    editor.relay.wait_for_reply(AWAIT)
    # While the widget waits for the run's first report, the run is still building.
    first_report = editor.relay.hold_replies(AWAIT)
    widget.run_button.click()
    first_report.wait_until_matched()
    expect(widget.text("Building…")).to_be_visible()
    first_report.release()
    # The test's output appears as it writes it, before the run is over.
    expect(widget.output).to_contain_text("step 1", timeout=RUN_TIMEOUT)
    expect(widget.text("Running…")).to_be_visible()
    expect(widget.output).not_to_contain_text("step 4")
    expect(widget.verdict("Passed")).to_have_count(0)
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "step 1\nstep 2\nstep 3\nstep 4\n")


def test_stderr_is_set_apart_from_stdout(editor):
    editor.show("Passing", "bothStreams")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "on stdout\non stderr\nstdout again\n")
    stderr = widget.output.locator("span", has_text="on stderr")
    stdout = widget.output.locator("span", has_text="on stdout")
    expect(stderr).to_have_css("font-style", "italic")
    expect(stdout).to_have_css("font-style", "normal")


def test_output_from_outside_the_capture_is_shown(editor):
    editor.show("Passing", "strayOutput")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect(widget.output).to_contain_text("captured")
    expect(widget.output).to_contain_text("stray output")
    stray_error = widget.output.locator("span", has_text="stray error")
    expect(stray_error).to_have_css("font-style", "italic")


def test_a_failed_build_is_reported_with_the_end_of_its_log(editor):
    editor.show("BuildError", "unbuildable")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("ERROR")
    expect(widget.messages.first).to_have_text("lake build failed")
    expect(widget.messages.nth(1)).to_contain_text("BuildError")
    expect(widget.seed_badge).to_have_count(0)


def test_a_runner_that_exits_early_is_reported_with_its_exit_code(editor):
    editor.show("Failing", "exits")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("ERROR")
    expect(widget.messages.first).to_have_text(
        "the test runner exited with code 3 before reporting an outcome"
    )


def test_each_output_box_copies_its_own_output_and_copy_all_copies_the_run(editor):
    editor.show("Passing", "copyOrder")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    # The test's own output is shown apart from the named result's, and each box copies its own.
    expect_exact_text(widget.output, "outer\nafter\n")
    widget.output.hover()
    widget.copy_button.click()
    expect(widget.copy_button).to_have_attribute("title", "Copied")
    assert editor.copied() == ["outer\nafter\n"]
    inner = widget.result("inner")
    inner.locator("> summary").click()
    inner.locator("> div pre").hover()
    inner.locator("> div").get_by_role(
        "button", name="Copy output to clipboard"
    ).click()
    assert editor.copied()[-1] == "within\n"
    # The run's output is in two boxes, so the title offers to copy all of it, in the order written.
    widget.copy_all.click()
    expect(widget.copy_all).to_have_attribute("title", "Copied")
    assert editor.copied()[-1] == "outer\nwithin\nafter\n"


def test_copy_all_is_offered_when_the_output_is_in_more_than_one_box(editor):
    editor.show("Passing", "bothStreams")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect(widget.copy_button).to_have_count(1)
    expect(widget.copy_all).to_have_count(0)


def test_the_test_docstring_is_shown_with_the_result(editor):
    editor.show("Passing", "bothStreams")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect(widget.root).to_contain_text("Writes to both streams.")
    expect(widget.root.get_by_text(re.compile(r"^· Run \d"))).to_be_visible()


def test_a_process_the_test_leaves_running_lets_the_run_end(editor):
    editor.show("Passing", "lingeringProcess")
    widget = Widget(editor.page)
    widget.run_button.click()
    # The helper holds the runner's output pipes open for over half a minute after the test has ended.
    widget.verdict("Passed").wait_for(timeout=20_000)
    expect_exact_text(widget.output, "started a helper\n")
    # The helper is ended with the run.
    wait_until(lambda: not matching("^sleep 37$"), timeout_ms=10_000)
    assert not matching("^sleep 37$"), "the helper outlived the run"


def test_a_rejected_start_is_followed_when_the_server_started_the_run(editor):
    editor.show("Passing", "bothStreams")
    widget = Widget(editor.page)
    editor.relay.wait_for_reply(AWAIT)
    # The server starts the run, and the page hears of a rejection, as it does when the InfoView
    # replaces the session while the call is out.
    editor.relay.reject_replies("Errata.Widget.startTest")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "on stdout\non stderr\nstdout again\n")
    expect(widget.text("could not run")).to_have_count(0)


def test_long_lines_of_multibyte_characters_arrive_whole(editor):
    editor.show("Passing", "wideCharacters")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    assert widget.output.text_content() == "∀" * 100_000 + "\n"


def test_tests_of_the_same_name_and_source_in_two_files_are_told_apart(editor):
    editor.show("TwinA", "twin")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "from TwinA\n")
    editor.move_to("TwinB", "twin")
    expect(widget.run_button).to_have_text("Run")
    expect(widget.verdict("Passed")).to_have_count(0)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "from TwinB\n")


def test_a_page_that_loads_again_shows_a_finished_run_as_it_was(editor):
    editor.show("Passing", "copyOrder")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    # A page that loads again has none of the run's output of its own, so the server sends it again.
    editor.reload_page()
    editor.show("Passing", "copyOrder")
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "outer\nafter\n")
    widget.result("inner").locator("> summary").click()
    expect_exact_text(widget.result_output("inner"), "within\n")


def test_a_docstring_over_several_lines_is_part_of_the_test(editor):
    editor.show_at_text("Passing", "whose closing delimiter follows its last text")
    widget = Widget(editor.page)
    expect(widget.title).to_contain_text("longDocstring")


def test_a_rejected_start_leaves_an_earlier_run_of_the_test_alone(editor):
    editor.show("Passing", "bothStreams")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    # A page that loads again shows the finished run from the server, and a Run from it that never
    # reaches the server is refused, with the earlier run left as the server's.
    editor.reload_page()
    editor.show("Passing", "bothStreams")
    widget.wait_for_verdict("Passed")
    editor.relay.reject_requests("Errata.Widget.startTest")
    widget.run_button.click()
    expect(widget.text("could not run: rejected by the test harness")).to_be_visible()


def test_a_test_marked_by_a_later_command_shows_its_widget_there(editor):
    editor.show_at_text("Passing", "attribute [test] markedSeparately")
    widget = Widget(editor.page)
    expect(widget.title).to_contain_text("markedSeparately")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "marked separately\n")


def test_an_attribute_list_over_two_lines_is_part_of_the_test(editor):
    editor.show_at_text("Passing", "def multiLineAttributes")
    widget = Widget(editor.page)
    expect(widget.title).to_contain_text("multiLineAttributes")
