"""Locators for the parts of the Errata widget that the tests look at and use, and checks on them."""

import re
import time

from playwright.sync_api import Locator, Page, expect

# How long a run may take, building included, in milliseconds.
RUN_TIMEOUT = 120_000

# How long an assertion waits for the page to show what it expects, in milliseconds. The page waits
# on a Lean server that may be opening a document or building a module, so this is generous.
EXPECT_TIMEOUT = 30_000

# The RPC methods of the widget that the tests hold, reject, or wait for replies to.
AWAIT = "Errata.Widget.awaitOutput"
CANCEL = "Errata.Widget.cancelTest"

# The decimal digits of the lines that the `slow` test writes.
TICK = re.compile(r"^tick (\d+)$")


def wait_until(check, timeout_ms: int = EXPECT_TIMEOUT, interval_s: float = 0.1):
    """
    Calls `check` until it returns a true value, and returns that value. Once `timeout_ms` has passed,
    the last value is returned whatever it is, for the caller to assert on.
    """
    deadline = time.monotonic() + timeout_ms / 1000
    while True:
        value = check()
        if value or time.monotonic() > deadline:
            return value
        time.sleep(interval_s)


def expect_exact_text(locator: Locator, text: str):
    """
    Waits until an element's text is `text`, newlines and all. Playwright's text assertions treat
    runs of whitespace as one space, so the text is matched that way first and then compared exactly.
    """
    expect(locator).to_have_text(text)
    assert locator.text_content() == text


def wait_for_html(locator: Locator, html: str):
    """Waits until an element's HTML is `html`."""
    wait_until(lambda: locator.inner_html() == html)
    assert locator.inner_html() == html


def ticks(locator: Locator) -> list[int]:
    """The numbers of the lines that the `slow` test wrote, in the order the element shows them."""
    lines = (locator.text_content() or "").split("\n")
    return [int(match[1]) for line in lines if (match := TICK.match(line))]


def wait_for_ticks(
    locator: Locator, count: int, timeout_ms: int = RUN_TIMEOUT
) -> list[int]:
    """
    Waits until the `slow` test has written at least `count` lines, and checks that they are shown
    each once, in order. Returns their numbers.
    """

    def enough():
        shown = ticks(locator) if locator.count() else []
        assert shown == list(range(len(shown))), shown
        return shown if len(shown) >= count else None

    shown = wait_until(enough, timeout_ms)
    if shown is None:
        raise TimeoutError(f"the slow test showed fewer than {count} lines")
    return shown


class Widget:
    """The Errata widget in the InfoView."""

    def __init__(self, page: Page):
        self.page = page
        self.root = page.locator("details:has(> summary:has-text('Errata test:'))")

    @property
    def title(self) -> Locator:
        return self.root.locator("> summary")

    @property
    def run_button(self) -> Locator:
        return self.root.get_by_role("button", name=re.compile(r"^Run( again)?$"))

    @property
    def cancel_button(self) -> Locator:
        return self.root.get_by_role("button", name="Cancel")

    @property
    def gear(self) -> Locator:
        return self.root.get_by_role("button", name="Run settings")

    @property
    def seed_field(self) -> Locator:
        return self.page.get_by_title(
            "Seed for property tests; blank chooses one randomly"
        )

    @property
    def add_option_button(self) -> Locator:
        return self.page.get_by_role("button", name="Add option")

    @property
    def option_rows(self) -> Locator:
        return self.page.get_by_role("group", name="Option")

    def add_option(self, name: str, value: str = "") -> None:
        """Adds a row to the open settings popup and fills it in."""
        self.add_option_button.click()
        row = self.option_rows.last
        row.get_by_title("Option name").fill(name)
        row.get_by_title("Option value; blank for a flag").fill(value)

    @property
    def expand_named(self) -> Locator:
        return self.page.get_by_label("Expand named results")

    @property
    def output(self) -> Locator:
        """The output of the test's own code."""
        return self.root.locator("details:has(> summary:has-text('Output')) pre").first

    @property
    def copy_button(self) -> Locator:
        """The copy button of the box that holds the output of the test's own code."""
        return self.root.locator(
            "details:has(> summary:has-text('Output'))"
        ).get_by_role("button", name="Copy output to clipboard")

    @property
    def copy_all(self) -> Locator:
        """The control in the title that copies the whole run's output."""
        return self.title.get_by_role("button", name="Copy all output")

    @property
    def messages(self) -> Locator:
        """The message and detail that the test's own code reported."""
        return self.root.locator("div.ml1 > div > div > pre")

    @property
    def source_buttons(self) -> Locator:
        return self.root.get_by_role("button", name=re.compile(r"^Go to "))

    @property
    def seed_badge(self) -> Locator:
        return self.root.get_by_role("button", name=re.compile(r"^Seed \d+$"))

    @property
    def options_badge(self) -> Locator:
        return self.root.get_by_role("button", name=re.compile(r"^Options "))

    def text(self, text: str) -> Locator:
        return self.root.get_by_text(text)

    def verdict(self, label: str) -> Locator:
        """The verdict of the run, such as `Passed` or `FAILED`."""
        return self.root.get_by_text(re.compile(f"^[✓✗⚠] {label}$"))

    def result(self, name: str) -> Locator:
        """A named result that opens to show what it reported."""
        return self.root.locator(
            f"details:has(> summary:text-matches('^\\\\S+ {name}(\\\\s|$)'))"
        )

    def result_output(self, name: str) -> Locator:
        """The output of a named result's own code, in its box."""
        return self.result(name).locator("> div > div > pre")

    def leaf(self, name: str) -> Locator:
        """A named result that reported nothing beyond its verdict, which has nothing to open."""
        return self.root.locator(
            f"div.errata-leaf:text-matches('^\\\\S+ {name}(\\\\s|$)')"
        )

    def wait_for_verdict(self, label: str):
        self.verdict(label).wait_for(timeout=RUN_TIMEOUT)
