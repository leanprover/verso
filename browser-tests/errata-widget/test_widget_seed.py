"""The seed for property tests."""

import re

import pytest
from playwright.sync_api import expect

from widget import Widget

pytestmark = pytest.mark.errata_widget


def test_a_property_test_shows_its_seed(editor):
    editor.show("Passing", "reverseReverse")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("Passed")
    expect(widget.seed_badge).to_be_visible()


def test_running_again_with_the_seed_reproduces_the_counterexample(editor):
    editor.show("Failing", "unluckyLists")
    widget = Widget(editor.page)
    widget.run_button.click()
    widget.wait_for_verdict("FAILED")
    seed = widget.seed_badge.inner_text()
    reported = widget.messages.all_inner_texts()
    assert any(re.search(r"\[\d+(, \d+){5,}\]", text) for text in reported), reported
    # Clicking the seed fills it in for the next run.
    widget.seed_badge.click()
    expect(widget.seed_field).to_have_value(seed.removeprefix("Seed "))
    editor.page.keyboard.press("Escape")
    expect(widget.gear).to_have_attribute("title", f"Run settings ({seed.lower()})")
    widget.run_button.click()
    expect(widget.verdict("FAILED")).to_have_count(0)
    widget.wait_for_verdict("FAILED")
    expect(widget.seed_badge).to_have_text(seed)
    assert widget.messages.all_inner_texts() == reported


def test_an_invalid_seed_blocks_the_run(editor):
    editor.show("Passing", "reverseReverse")
    widget = Widget(editor.page)
    widget.gear.click()
    widget.seed_field.fill("12ab")
    expect(editor.page.get_by_text("The seed must be a natural number")).to_be_visible()
    expect(widget.text("invalid seed — see run settings")).to_be_visible()
    expect(widget.run_button).to_be_disabled()
    widget.seed_field.fill("12")
    expect(widget.text("invalid seed — see run settings")).to_have_count(0)
    expect(widget.run_button).to_be_enabled()
