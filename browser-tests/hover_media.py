import pytest
from playwright.sync_api import Page


def require_hover_media(page: Page):
    """Skip when the browser reports no hover support, which disables CSS guarded by
    @media (hover: hover). Linux headless Firefox does this:
    https://bugzilla.mozilla.org/show_bug.cgi?id=2037020

    A test that calls this carries the marker `hover_media`. Under Errata a skip is an error, and
    the `ci` profile's default filter leaves out these tests on Firefox."""
    if not page.evaluate("matchMedia('(hover: hover)').matches"):
        pytest.skip("Browser does not enable CSS guarded by @media (hover: hover)")
