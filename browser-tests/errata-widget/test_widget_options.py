"""The options that a run passes to the test."""

import pytest
from playwright.sync_api import expect

from widget import Widget, expect_exact_text

pytestmark = pytest.mark.errata_widget


def test_the_options_reach_the_test(editor):
    editor.show("Passing", "readsOptions")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.add_option("greeting", "hello")
    widget.add_option("greeting", "good day")
    editor.page.keyboard.press("Escape")
    # The gear names the options as the command line writes them while the settings are closed.
    expect(widget.gear).to_have_attribute(
        "title", 'Run settings (options --greeting=hello --greeting="good day")'
    )
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "greeting: hello\ngreeting: good day\n")


def test_a_value_is_passed_as_written(editor):
    editor.show("Passing", "readsOptions")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.add_option("greeting", '-x "quoted" a=b')
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, 'greeting: -x "quoted" a=b\n')


def test_a_flag_option_reaches_the_test(editor):
    editor.show("Passing", "readsOptions")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.add_option("strict")
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("FAILED")
    expect(widget.messages.first).to_have_text("strict was set")


def test_an_option_without_a_name_holds_back_the_run(editor):
    editor.show("Passing", "readsOptions")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.add_option("", "hello")
    # The popup is outside the widget, so its hint is found on the page.
    expect(editor.page.get_by_text("Each option needs a name")).to_be_visible()
    editor.page.keyboard.press("Escape")
    expect(widget.run_button).to_have_attribute("title", "Each option needs a name")
    expect(widget.text("invalid option — see run settings")).to_be_visible()
    widget.gear.click()
    widget.option_rows.last.get_by_title("Option name").fill("greeting")
    editor.page.keyboard.press("Escape")
    expect(widget.text("invalid option — see run settings")).to_have_count(0)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "greeting: hello\n")


def test_a_name_written_with_its_dashes_holds_back_the_run(editor):
    editor.show("Passing", "readsOptions")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.add_option("--greeting", "hello")
    hint = "Write each option's name without its leading dashes"
    expect(editor.page.get_by_text(hint)).to_be_visible()
    editor.page.keyboard.press("Escape")
    expect(widget.run_button).to_have_attribute("title", hint)


def test_a_removed_option_is_not_passed(editor):
    editor.show("Passing", "readsOptions")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.add_option("strict")
    widget.add_option("greeting", "hello")
    widget.option_rows.first.get_by_role("button", name="Remove option").click()
    expect(widget.option_rows).to_have_count(1)
    expect(widget.option_rows.first.get_by_title("Option name")).to_have_value(
        "greeting"
    )
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "greeting: hello\n")


def test_a_run_removes_the_blank_options(editor):
    editor.show("Passing", "readsOptions")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.add_option("")
    widget.add_option("greeting", "hello")
    widget.add_option("")
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    widget.gear.click()
    expect(widget.option_rows).to_have_count(1)
    expect(widget.option_rows.first.get_by_title("Option name")).to_have_value(
        "greeting"
    )


def test_removing_an_option_moves_the_focus_to_its_neighbour(editor):
    editor.show("Passing", "readsOptions")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.add_option("first")
    widget.add_option("second")
    widget.option_rows.first.get_by_role("button", name="Remove option").click()
    expect(widget.option_rows.first.get_by_title("Option name")).to_be_focused()
    widget.option_rows.first.get_by_role("button", name="Remove option").click()
    expect(widget.add_option_button).to_be_focused()


def test_the_options_of_a_run_can_be_used_again(editor):
    editor.show("Passing", "readsOptions")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.add_option("greeting", "good day")
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect(widget.options_badge).to_have_text('Options --greeting="good day"')
    # Showing another test and coming back restores the result, whose badge fills the settings.
    editor.move_to("Passing", "bothStreams")
    expect(widget.title).to_contain_text("bothStreams")
    editor.move_to("Passing", "readsOptions")
    expect(widget.title).to_contain_text("readsOptions")
    expect(widget.option_rows).to_have_count(0)
    widget.options_badge.click()
    expect(widget.option_rows).to_have_count(1)
    expect(
        widget.option_rows.first.get_by_title("Option value; blank for a flag")
    ).to_have_value("good day")
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "greeting: good day\n")


def test_the_settings_scroll_when_they_outgrow_the_window(editor):
    editor.page.set_viewport_size({"width": 900, "height": 360})
    editor.show("Passing", "readsOptions")
    widget = Widget(editor.page)
    widget.gear.click()
    # Each row is added with the button below the rows, which the popup scrolls to.
    for i in range(12):
        widget.add_option(f"option{i}")
    expect(widget.option_rows).to_have_count(12)


def test_an_option_the_test_never_read_is_named(editor):
    editor.show("Passing", "readsOptions")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.add_option("greeting", "hello")
    widget.add_option("colour", "red")
    widget.add_option("size", "large")
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect(widget.text("options never read by this test: colour, size")).to_be_visible()
    # The rows of the options that were never read are marked in the settings.
    widget.gear.click()
    marked = widget.option_rows.filter(has=editor.page.get_by_label("Never read"))
    expect(marked).to_have_count(2)
    expect(marked.first.get_by_title("Option name")).to_have_value("colour")
    # A run that reads every option it is given names none.
    widget.option_rows.nth(2).get_by_role("button", name="Remove option").click()
    widget.option_rows.nth(1).get_by_role("button", name="Remove option").click()
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect(widget.text("never read by this test")).to_have_count(0)
    widget.gear.click()
    expect(editor.page.get_by_label("Never read")).to_have_count(0)
