"""The tree of named results, and the links from failures to the checks that failed."""

import re

import pytest
from playwright.sync_api import expect

from widget import Widget, expect_exact_text

pytestmark = pytest.mark.errata_widget


def line_of(editor, module, text):
    """The line, counted from zero, of the first line of a fixture module that contains `text`."""
    lines = editor.path(module).read_text(encoding="utf-8").split("\n")
    return next(i for i, line in enumerate(lines) if text in line)


def test_named_results_start_closed_and_open_only_with_something_to_show(editor):
    editor.show("Passing", "nested")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "setting up\n")
    # A result with output or results inside it is a disclosure, closed at first.
    parsing = widget.result("parsing")
    expect(parsing).to_have_count(1)
    expect(parsing).not_to_have_attribute("open", "")
    # A result that reported nothing beyond its verdict has nothing to open.
    expect(widget.leaf("silent")).to_have_count(1)
    expect(widget.result("silent")).to_have_count(0)
    parsing.locator("> summary").click()
    expect(parsing).to_have_attribute("open", "")
    expect_exact_text(widget.result_output("parsing").first, "reading\n")
    expect(widget.result("tokens")).not_to_have_attribute("open", "")
    expect(widget.leaf("quiet")).to_have_count(1)


def test_the_expand_setting_opens_every_named_result(editor):
    editor.show("Passing", "nested")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    widget.gear.click()
    widget.expand_named.check()
    expect(widget.result("parsing")).to_have_attribute("open", "")
    expect(widget.result("tokens")).to_have_attribute("open", "")
    expect_exact_text(widget.result_output("tokens"), "12 tokens\n")
    widget.expand_named.uncheck()
    expect(widget.result("parsing")).not_to_have_attribute("open", "")


def test_a_failure_in_the_test_itself_shows_its_message_and_where_it_is(editor):
    editor.show("Failing", "ownFailure")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("FAILED")
    expect(widget.messages.first).to_have_text("the check failed")
    expect_exact_text(widget.output, "before the failure\n")
    line = line_of(editor, "Failing", 'fail "the check failed"')
    expect(widget.source_buttons).to_have_count(1)
    expect(widget.source_buttons).to_have_attribute(
        "title", re.compile(f"^Go to Failing.lean:{line + 1}:")
    )
    widget.source_buttons.click()
    editor.page.wait_for_function("window.harness.editorCalls.length > 0")
    [call] = editor.editor_calls()
    assert call["kind"] == "showDocument"
    assert call["show"]["uri"] == editor.path("Failing").as_uri()
    assert call["show"]["selection"]["start"]["line"] == line


def test_the_path_to_a_failure_is_open_and_only_the_failed_check_has_a_link(editor):
    editor.show("Failing", "nestedFailure")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("FAILED")
    # The results that contain the failure are open, and the one that passed is closed.
    expect(widget.result("outer")).to_have_attribute("open", "")
    expect(widget.result("inner")).to_have_attribute("open", "")
    expect(widget.result("fine")).not_to_have_attribute("open", "")
    # Only the failed check links to a place in the source: `outer` failed because `inner` did.
    expect(widget.source_buttons).to_have_count(1)
    expect(
        widget.result("inner").locator("> summary").get_by_role("button")
    ).to_have_count(1)
    expect(
        widget.result("outer").locator("> summary").get_by_role("button")
    ).to_have_count(0)
    line = line_of(editor, "Failing", "assertBEq 1 2")
    widget.source_buttons.click()
    editor.page.wait_for_function("window.harness.editorCalls.length > 0")
    [call] = editor.editor_calls()
    assert call["show"]["selection"]["start"]["line"] == line


def test_a_link_counts_columns_as_the_editor_does(editor):
    editor.show("Failing", "astralFailure")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("FAILED")
    line = line_of(editor, "Failing", 'result "🙂🙂"')
    text = editor.path("Failing").read_text(encoding="utf-8").split("\n")[line]
    before = text[: text.index("assertBEq")]
    widget.result("🙂🙂").locator("> summary").get_by_role("button").click()
    editor.page.wait_for_function("window.harness.editorCalls.length > 0")
    [call] = editor.editor_calls()
    start = call["show"]["selection"]["start"]
    assert start["line"] == line
    # Each emoji is one codepoint and two UTF-16 code units.
    assert start["character"] == len(before.encode("utf-16-le")) // 2
    assert start["character"] == len(before) + 2
    # The tooltip counts lines and columns from one, as the editor's status bar does.
    expect(
        widget.result("🙂🙂").locator("> summary").get_by_role("button")
    ).to_have_attribute(
        "title", f"Go to Failing.lean:{line + 1}:{start['character'] + 1}"
    )


def test_a_failure_within_expect_fail_shows_as_expected(editor):
    editor.show("Passing", "expectedFailure")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expected = widget.result("expected")
    expect(expected.locator("> summary [role=img]")).to_have_attribute(
        "aria-label", "Expected failure"
    )
    # A failure that the test expected is no reason to open the tree.
    expect(expected).not_to_have_attribute("open", "")
    expected.locator("> summary").click()
    expect(expected.locator("> div > pre").first).to_have_text("values are not equal")


def test_an_assert_true_message_is_shown(editor):
    editor.show("Failing", "ownAssertTrue")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("FAILED")
    expect(widget.messages.first).to_have_text(
        "the message of the top-level assertTrue"
    )
    editor.move_to("Failing", "nestedAssertTrue")
    expect(widget.title).to_contain_text("nestedAssertTrue")
    widget.run_button.click()
    widget.wait_for_verdict("FAILED")
    condition = widget.result("condition")
    expect(condition).to_have_attribute("open", "")
    expect(condition.locator("> div > pre").first).to_have_text(
        "the message of the nested assertTrue"
    )


def test_a_failure_within_an_interrupted_expect_fail_is_expected_by_the_one_around_it(
    editor,
):
    editor.show("Passing", "nestedExpectFail")
    widget = Widget(editor.page)
    widget.run_button.click()
    # The error that escaped the named result stays in the test's results.
    widget.wait_for_verdict("ERROR")
    widget.gear.click()
    widget.expand_named.check()
    expect(widget.result("inner").locator("> summary [role=img]")).to_have_attribute(
        "aria-label", "Expected failure"
    )
