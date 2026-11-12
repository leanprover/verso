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


SECTION = "Verso.Genre.Manual.section"
EXAMPLE = "Verso.Genre.Manual.example"


class TestFindPage:
    """Tests for the messages that the redirect page shows when it can't redirect."""

    def open_find(self, server: str, page: Page, query: str) -> list[str]:
        """Opens the redirect page with a query string and returns the page errors."""
        errors: list[str] = []
        page.on("pageerror", lambda e: errors.append(str(e)))
        page.goto(f"{server}/find/?{query}")
        page.wait_for_load_state("networkidle")
        return errors

    def test_not_found(self, server: str, page: Page):
        errors = self.open_find(server, page, f"name=no-such-name&domain={SECTION}")
        expect(page).to_have_title("Not found: 'no-such-name'")
        expect(page.locator("#message code").first).to_have_text("no-such-name")
        expect(page.locator("#message li")).to_contain_text([SECTION])
        assert errors == []

    def test_unknown_domain(self, server: str, page: Page):
        errors = self.open_find(server, page, "name=website&domain=No.Such.Domain")
        expect(page).to_have_title("Not found: 'website'")
        expect(page.locator("#message")).to_contain_text("This domain does not exist:")
        expect(page.locator("#message li code")).to_have_text(["No.Such.Domain"])
        expect(page.locator("#message")).to_contain_text("No domains were searched.")
        assert errors == []

    def test_no_name(self, server: str, page: Page):
        errors = self.open_find(server, page, f"domain={SECTION}")
        expect(page).to_have_title("No name provided")
        assert errors == []

    def test_repeated_domain(self, server: str, page: Page):
        """A domain that is requested twice still yields a single match."""
        errors = self.open_find(server, page, f"name=website&domain={SECTION}&domain={SECTION}")
        expect(page).to_have_url(re.compile(r"#website$"))
        assert errors == []

    def test_ambiguous_within_domain(self, server: str, page: Page):
        errors = self.open_find(server, page, f"name=mkList&domain={EXAMPLE}")
        expect(page).to_have_title("Ambiguous: 'mkList'")
        links = page.locator("#message a")
        assert links.count() >= 2
        for href in links.evaluate_all("as => as.map(a => a.href)"):
            assert href.startswith(f"{server}/"), href
            assert "#" in href, href
        assert errors == []
