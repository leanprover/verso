"""Tests for a page that mounts rendered HTML content.

The document carries the scripts of two Verso releases at once: the site's own, which reach the
markup that the site rendered, and the mounted content's, which reach the markup that shipped with
it. Nothing static shows how they behave together, so these tests drive a browser.
"""

from playwright.sync_api import expect, Page

MOUNTED_PAGE = "/tutorials/v1/hashmap/"

# The site's own content on a mounted page.
SITE_MATH = "#site-math"
SITE_TOKEN = "#site-token"

# The mounted content's own markup.
MOUNTED = ".verso-content.content"


class TestMountedContent:
    def test_math_is_rendered_once(self, server: str, page: Page):
        page.goto(f"{server}{MOUNTED_PAGE}")
        page.wait_for_load_state("networkidle")

        math = page.locator(".math.inline, .math.display")
        expect(math).not_to_have_count(0)
        for i in range(math.count()):
            expect(math.nth(i).locator(".katex")).to_have_count(1)

        # Both the site's own math and the mounted content's math are rendered.
        expect(page.locator(f"{SITE_MATH} .katex")).to_have_count(1)
        expect(page.locator(f"{MOUNTED} .math.inline .katex")).not_to_have_count(0)

    def test_hovers_work_on_the_sites_own_code(self, server: str, page: Page):
        page.goto(f"{server}{MOUNTED_PAGE}")
        page.wait_for_load_state("networkidle")

        page.locator(SITE_TOKEN).hover()
        expect(page.locator("[data-tippy-root]")).not_to_have_count(0)

    def test_hovers_work_on_the_mounted_code(self, server: str, page: Page):
        page.goto(f"{server}{MOUNTED_PAGE}")
        page.wait_for_load_state("networkidle")

        token = page.locator(f"{MOUNTED} .hl.lean .const.token").first
        expect(token).to_be_visible()
        token.hover()
        expect(page.locator("[data-tippy-root]")).not_to_have_count(0)

    def test_the_wrappers_are_separate(self, server: str, page: Page):
        page.goto(f"{server}{MOUNTED_PAGE}")
        page.wait_for_load_state("networkidle")

        # The mounted content is marked as Verso content, and the site's own code on the same
        # page is not, which is what keeps the two releases' scripts off each other's markup.
        expect(page.locator(f"{MOUNTED}[data-verso-docs]")).to_have_count(1)
        expect(page.locator(f"{SITE_TOKEN}").locator("xpath=ancestor::*[contains(@class,'verso-content')]")).to_have_count(0)
