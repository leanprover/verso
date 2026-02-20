from playwright.sync_api import expect, Page


class TestContent:
    def test_code_boxes_present(self, server: str, page: Page):
        """Test that module pages contain code boxes."""
        page.goto(f"{server}/LitConfig/")

        code_boxes = page.locator(".code-box")
        expect(code_boxes.first).to_be_visible()

    def test_prose_content(self, server: str, page: Page):
        """Test that module docstrings appear as prose content."""
        page.goto(f"{server}/LitConfig/")

        # The LitConfig module has "A Test Module" in its module docstring
        main = page.locator("#main-content")
        expect(main).to_contain_text("A Test Module")

    def test_no_docstrings_page(self, server: str, page: Page):
        """Test that a module with no docstrings has code boxes but no module doc prose."""
        page.goto(f"{server}/LitConfig/NoDocstrings/")

        # Should have code boxes
        code_boxes = page.locator(".code-box")
        expect(code_boxes.first).to_be_visible()

        # Should not have module docstring elements
        mod_docs = page.locator(".verso-text.mod-doc")
        expect(mod_docs).to_have_count(0)

    def test_collapsible_imports(self, server: str, page: Page):
        """Test that the imports list is collapsible."""
        page.goto(f"{server}/LitConfig/")

        imports_list = page.locator("details.imports-list")
        # It may or may not exist depending on whether this module has imports
        # that are rendered; if it exists, it should be toggleable
        if imports_list.count() > 0:
            summary = imports_list.locator("summary")
            expect(summary).to_be_visible()
            summary.click()
            expect(imports_list).to_have_attribute("open", "")

    def test_copy_button(self, server: str, page: Page):
        """Test that code boxes have copy buttons."""
        page.goto(f"{server}/LitConfig/")

        # Hover over a code box to reveal the copy button
        code_box = page.locator(".code-box").first
        code_box.hover()

        copy_btn = code_box.locator(".copy-button")
        expect(copy_btn).to_be_visible()
