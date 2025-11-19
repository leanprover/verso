

import pytest
import re
from playwright.sync_api import expect, Page

class TestRedirect:
    def test_redirect(self, server: str, page: Page, redirect_case: tuple[str, str]):
        """Test that the redirect page navigates to the correct target."""
        source, target = redirect_case

        # TODO: adjust URL construction to match your redirect page
        # e.g., if your redirect page is at /go and uses ?target=...
        page.goto(f"{server}/find/?domain=Verso.Genre.Manual.section&name={source}")

        # TODO: adjust expected URL pattern
        # This assumes target is the final URL path
        expect(page).to_have_url(re.compile(re.escape(target)))
