import pytest
from playwright.sync_api import Page


def require_hover_media(page: Page):
    """Skip when the browser reports no hover support, which disables CSS guarded by
    @media (hover: hover). Linux headless Firefox does this:
    https://bugzilla.mozilla.org/show_bug.cgi?id=2037020

    All tests that call this function are tagged `hover_media`. Under Errata a skip is an error, so
    the `ci` profile's default filter excludes these tests from Firefox runs."""
    if not page.evaluate("matchMedia('(hover: hover)').matches"):
        pytest.skip("Browser does not enable CSS guarded by @media (hover: hover)")
