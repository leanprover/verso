"""
The fields for the settings that a test declares, which start with the values that the profile of
the fixture workspace's `errata.toml` gives them.
"""

import pytest
from playwright.sync_api import expect

from widget import Widget, expect_exact_text

pytestmark = pytest.mark.errata_widget


def test_the_fields_start_with_the_profile_and_the_run_uses_it(editor):
    editor.show("Passing", "readsSettings")
    widget = Widget(editor.page)
    widget.gear.click()
    expect(widget.setting_rows).to_have_count(2)
    expect(widget.setting_field("greeting")).to_have_value("good day")
    # A setting that the profile leaves out starts blank, and the field says what the test gets.
    expect(widget.setting_field("strict")).to_have_value("")
    expect(widget.setting_field("strict")).to_have_attribute("placeholder", "unset")
    editor.page.keyboard.press("Escape")
    expect(widget.gear).to_have_attribute("title", "Run settings")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "greeting: good day\n")
    expect(widget.settings_badge).to_have_text('Settings "greeting=good day"')


def test_a_changed_value_reaches_the_test(editor):
    editor.show("Passing", "readsSettings")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.setting_field("greeting").fill('-x "quoted" a=b')
    editor.page.keyboard.press("Escape")
    # The gear names the values that differ from the profile's while the settings are closed.
    expect(widget.gear).to_have_attribute(
        "title", 'Run settings (settings "greeting=-x \\"quoted\\" a=b")'
    )
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, 'greeting: -x "quoted" a=b\n')


def test_an_optional_setting_reaches_the_test(editor):
    editor.show("Passing", "readsSettings")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.setting_field("strict").fill("true")
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("FAILED")
    expect(widget.messages.first).to_have_text("strict was set")


def test_a_value_that_the_setting_rejects_ends_the_test_with_an_error(editor):
    editor.show("Passing", "readsSettings")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.setting_field("strict").fill("maybe")
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("ERROR")
    expect(widget.messages.first).to_contain_text(
        'the setting strict has the value "maybe", which its parser rejects'
    )


def test_an_emptied_optional_field_leaves_its_setting_unset(editor):
    editor.show("Passing", "readsSettings")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.setting_field("strict").fill("true")
    widget.setting_field("strict").fill("")
    expect(widget.setting_field("strict")).to_have_attribute("placeholder", "unset")
    editor.page.keyboard.press("Escape")
    expect(widget.gear).to_have_attribute("title", "Run settings")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")


def test_an_emptied_field_with_a_profile_value_sends_the_empty_value(editor):
    editor.show("Passing", "readsSettings")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.setting_field("greeting").fill("")
    expect(widget.setting_field("greeting")).to_have_attribute("placeholder", "empty")
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "greeting: \n")


def test_the_reset_button_restores_the_profiles_value(editor):
    editor.show("Passing", "readsSettings")
    widget = Widget(editor.page)
    widget.gear.click()
    reset = editor.page.get_by_role("button", name="Use the profile's value")
    expect(reset).to_have_count(0)
    widget.setting_field("greeting").fill("hi")
    reset.click()
    expect(widget.setting_field("greeting")).to_have_value("good day")
    expect(reset).to_have_count(0)
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "greeting: good day\n")


def test_the_settings_of_a_run_can_be_used_again(editor):
    editor.show("Passing", "readsSettings")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.setting_field("greeting").fill("hi")
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect(widget.settings_badge).to_have_text("Settings greeting=hi")
    # Showing another test and coming back restores the result, whose badge fills the settings.
    editor.move_to("Passing", "bothStreams")
    expect(widget.title).to_contain_text("bothStreams")
    editor.move_to("Passing", "readsSettings")
    expect(widget.title).to_contain_text("readsSettings")
    widget.gear.click()
    expect(widget.setting_field("greeting")).to_have_value("good day")
    editor.page.keyboard.press("Escape")
    widget.settings_badge.click()
    expect(widget.setting_field("greeting")).to_have_value("hi")
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "greeting: hi\n")


def test_a_test_without_settings_has_no_fields(editor):
    editor.show("Passing", "bothStreams")
    widget = Widget(editor.page)
    widget.gear.click()
    expect(widget.seed_field).to_be_visible()
    expect(widget.setting_rows).to_have_count(0)
    expect(editor.page.get_by_text("Settings:")).to_have_count(0)


def test_the_seed_goes_to_the_seed_setting_and_has_no_field_of_its_own(editor):
    editor.show("Passing", "reverseReverse")
    widget = Widget(editor.page)
    widget.gear.click()
    expect(widget.setting_rows).to_have_count(0)
    widget.seed_field.fill("12345")
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect(widget.seed_badge).to_have_text("Seed 12345")


def run_once_for_the_configuration(widget: Widget):
    """
    Runs the shown test, so that the driver has elaborated the workspace's configuration, whose
    profiles the widget then offers.
    """
    widget.run_button.click()
    widget.wait_for_verdict("Passed")


def test_switching_profiles_changes_the_prefilled_values(editor):
    editor.show("Passing", "readsSettings")
    widget = Widget(editor.page)
    run_once_for_the_configuration(widget)
    widget.gear.click()
    expect(widget.profile_menu).to_have_value("default")
    expect(widget.profile_menu.locator("option")).to_have_text(["default", "ci"])
    expect(widget.setting_field("greeting")).to_have_value("good day")
    widget.profile_menu.select_option("ci")
    expect(widget.setting_field("greeting")).to_have_value("good evening")
    widget.profile_menu.select_option("default")
    expect(widget.setting_field("greeting")).to_have_value("good day")
    # A value that the reader typed stays when the profile changes.
    widget.setting_field("greeting").fill("hi")
    widget.profile_menu.select_option("ci")
    expect(widget.setting_field("greeting")).to_have_value("hi")


def test_a_run_under_a_profile_passes_it_to_the_driver(editor):
    editor.show("Passing", "readsSettings")
    widget = Widget(editor.page)
    run_once_for_the_configuration(widget)
    widget.gear.click()
    widget.profile_menu.select_option("ci")
    editor.page.keyboard.press("Escape")
    expect(widget.gear).to_have_attribute("title", "Run settings (profile ci)")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    # The field was left as the profile gives it, so the greeting comes from `-P ci` alone.
    expect_exact_text(widget.output, "greeting: good evening\n")


def test_a_test_that_no_profile_selects_runs_under_the_default_as_the_fallback(editor):
    editor.show("Passing", "readsSettings")
    widget = Widget(editor.page)
    run_once_for_the_configuration(widget)
    editor.move_to("Passing", "manualOnly")
    expect(widget.title).to_contain_text("manualOnly")
    widget.gear.click()
    expect(widget.profile_menu.locator("option")).to_have_text(["default (fallback)"])
    expect(editor.page.get_by_text("No profile's default filter selects this test")).to_be_visible()
    editor.page.keyboard.press("Escape")
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect_exact_text(widget.output, "ran by hand\n")
