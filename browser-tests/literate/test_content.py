import re

from playwright.sync_api import expect, Page


class TestContent:
    """Tests for page content: code boxes, prose, docstrings, commands, copy button, etc."""

    def test_code_boxes_present(self, server: str, page: Page):
        """Test that module pages contain .code-box elements."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        code_boxes = page.locator(".code-box")
        expect(code_boxes.first).to_be_visible()
        assert code_boxes.count() >= 1

    def test_prose_from_module_docstrings(self, server: str, page: Page):
        """Test that module docstring text appears in .mod-doc elements."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        # LitConfig has /-! # LitConfig: A Test Module ... -/
        mod_docs = page.locator(".mod-doc")
        expect(mod_docs.first).to_be_visible()
        expect(mod_docs.first).to_contain_text("A Test Module")

    def test_prose_and_code_interleaving(self, server: str, page: Page):
        """Test that prose (.mod-doc) and code (.code-box) alternate in source order."""
        page.goto(f"{server}/LitConfig/Core/")
        page.wait_for_load_state("networkidle")

        # Core has: /-! # Core Module -/, /-! ## Natural Number Utilities -/,
        # def double, def triple, /-! Here are some examples: -/, #eval double 5, #eval triple 5
        # So we expect mod-doc and code-box elements interleaved.
        content = page.locator(".code-content")
        # Collect all mod-doc and code-box children in order
        elements = content.locator(":scope > .mod-doc, :scope > .code-box")
        count = elements.count()
        assert count >= 3, (
            f"Expected at least 3 content elements (mod-doc + code-box), got {count}"
        )

        # Verify we have both types
        classes = [elements.nth(i).evaluate("el => el.className") for i in range(count)]
        has_mod_doc = any("mod-doc" in c for c in classes)
        has_code_box = any("code-box" in c for c in classes)
        assert has_mod_doc, "Expected mod-doc elements in content"
        assert has_code_box, "Expected code-box elements in content"

    def test_no_docstrings_page(self, server: str, page: Page):
        """Test that NoDocstrings page has code boxes but no mod-doc prose."""
        page.goto(f"{server}/LitConfig/NoDocstrings/")
        page.wait_for_load_state("networkidle")

        # Should have code boxes
        code_boxes = page.locator(".code-box")
        expect(code_boxes.first).to_be_visible()

        # Should not have module docstring elements
        verso_mod_docs = page.locator(".verso-text.mod-doc")
        expect(verso_mod_docs).to_have_count(0)
        md_mod_docs = page.locator(".md-text.mod-doc")
        expect(md_mod_docs).to_have_count(0)

    def test_declaration_docstrings_in_code_boxes(self, server: str, page: Page):
        """Test that declaration docstrings appear inside code boxes."""
        page.goto(f"{server}/LitConfig/Core/")
        page.wait_for_load_state("networkidle")

        # Core has /-- Doubles a natural number. -/ and /-- Triples a natural number. -/
        # These should appear as .verso-text (non-mod-doc) inside .code-box elements
        main = page.locator("#main-content")
        expect(main).to_contain_text("Doubles a natural number")
        expect(main).to_contain_text("Triples a natural number")

    def test_command_output(self, server: str, page: Page):
        """Test that #eval output appears in .lean-output elements."""
        page.goto(f"{server}/LitConfig/Core/")
        page.wait_for_load_state("networkidle")

        # Core has #eval double 5 (= 10) and #eval triple 5 (= 15)
        outputs = page.locator(".lean-output")
        expect(outputs.first).to_be_visible()
        assert outputs.count() >= 1

        # At least one output should contain "10" (from double 5)
        main = page.locator("#main-content")
        expect(main).to_contain_text("10")

    def test_command_output_interleaving(self, server: str, page: Page):
        """Test that each command's output appears right after its code, not batched."""
        page.goto(f"{server}/LitConfig/Core/Basic/")
        page.wait_for_load_state("networkidle")

        # Core/Basic has #check ident followed by #eval ident 42
        # The outputs should be interleaved with the code, not grouped at the end
        code_box = page.locator(".code-box").first
        children = code_box.locator(":scope > *")
        count = children.count()
        assert count >= 2, f"Expected at least 2 children in code-box, got {count}"

        # Walk child elements and verify outputs don't all come after all code
        # We expect: code, output, code, output (not: code, code, output, output)
        types = []
        for i in range(count):
            child = children.nth(i)
            cls = child.get_attribute("class") or ""
            if "lean-output" in cls:
                types.append("output")
            elif child.evaluate("el => el.tagName") in ["PRE", "DIV", "CODE"]:
                types.append("code")

        # There should be at least one output that is NOT at the end after all code
        # i.e., the pattern should not be [code, code, ..., output, output, ...]
        first_output = next((i for i, t in enumerate(types) if t == "output"), None)
        last_code = next(
            (len(types) - 1 - i for i, t in enumerate(reversed(types)) if t == "code"),
            None,
        )
        if first_output is not None and last_code is not None:
            assert first_output < last_code, (
                f"Outputs are batched after all code blocks instead of interleaved: {types}"
            )

    def test_code_box_no_line_numbers(self, server: str, page: Page):
        """Test that code boxes do not contain line number elements."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        # There should be no .line-number or .line-numbers elements
        line_numbers = page.locator(".code-box .line-number, .code-box .line-numbers")
        expect(line_numbers).to_have_count(0)

    def test_collapsible_imports_toggle(self, server: str, page: Page):
        """Test that details.imports-list opens and closes, showing import code."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        imports_list = page.locator("details.imports-list")
        assert imports_list.count() >= 1, "Expected imports-list details element"

        # Should be collapsed by default
        assert not imports_list.evaluate("el => el.open"), (
            "imports-list should be collapsed by default"
        )

        # Click summary to open
        summary = imports_list.locator("summary")
        expect(summary).to_be_visible()
        summary.click()
        expect(imports_list).to_have_attribute("open", "")

        # Should show highlighted import code inside
        code = imports_list.locator(".imports-code .hl.lean")
        assert code.count() >= 1, "Expected highlighted import code"

        # Close it
        summary.click()
        expect(imports_list).not_to_have_attribute("open", "")

    def test_copy_button_on_hover(self, server: str, page: Page):
        """Test that .copy-button is only visible when hovering over its .code-box."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        code_box = page.locator(".code-box").first
        copy_btn = code_box.locator(".copy-button")

        # Before hover: opacity should be 0 (CSS: .copy-button { opacity: 0 })
        opacity = copy_btn.evaluate("el => getComputedStyle(el).opacity")
        assert opacity == "0", (
            f"Expected copy button opacity 0 before hover, got {opacity}"
        )

        # Verify the CSS rule exists: .code-box:hover .copy-button { opacity: 1 }
        has_hover_rule = page.evaluate("""() => {
            for (const sheet of document.styleSheets) {
                try {
                    for (const rule of sheet.cssRules) {
                        if (rule.selectorText && rule.selectorText.includes('.code-box:hover .copy-button')) {
                            return rule.style.opacity === '1';
                        }
                    }
                } catch (e) { /* cross-origin sheets */ }
            }
            return false;
        }""")
        assert has_hover_rule, (
            "Expected CSS rule .code-box:hover .copy-button { opacity: 1 }"
        )

    def test_copy_button_click(self, server: str, page: Page):
        """Test that clicking the copy button adds .copied class."""
        # Grant clipboard-write permission (Chromium only; Firefox doesn't support this)
        try:
            page.context.grant_permissions(["clipboard-write", "clipboard-read"])
        except Exception:
            pass  # Firefox doesn't support clipboard permissions via grant_permissions

        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        code_box = page.locator(".code-box").first
        # Force-click the copy button (it has opacity 0 but is in the DOM)
        copy_btn = code_box.locator(".copy-button")
        copy_btn.click(force=True)

        # Should have .copied class and show "Copied!" text
        expect(copy_btn).to_have_class(re.compile(r"\bcopied\b"))
        expect(copy_btn).to_have_text("Copied!")

    def test_landing_page(self, server: str, page: Page):
        """Test that / has .landing-page with .module-toc linking to modules."""
        page.goto(f"{server}/")
        page.wait_for_load_state("networkidle")

        landing = page.locator(".landing-page")
        expect(landing).to_be_visible()

        # Should have a module table of contents (may be nested <ul>s)
        toc = page.locator(".module-toc").first
        expect(toc).to_be_visible()

        # Should have links to modules
        links = landing.locator(".module-toc a")
        assert links.count() >= 1, "Expected at least one module link in the ToC"

        # The links should include our test modules
        landing_text = landing.inner_text()
        assert "LitConfig" in landing_text, "Expected LitConfig in module ToC"

    def test_no_empty_code_boxes(self, server: str, page: Page):
        """Test that no page in the site has an empty code-box."""
        pages_to_check = [
            "/LitConfig/",
            "/LitConfig/Core/",
            "/LitConfig/Core/Basic/",
            "/LitConfig/NoDocstrings/",
        ]
        for path in pages_to_check:
            page.goto(f"{server}{path}")
            page.wait_for_load_state("networkidle")

            code_boxes = page.locator(".code-box")
            for i in range(code_boxes.count()):
                box = code_boxes.nth(i)
                text = box.inner_text().strip()
                assert text, f"Empty code-box found on {path} (box {i})"

    def test_page_title(self, server: str, page: Page):
        """Test that <h1> text matches the module name."""
        page.goto(f"{server}/LitConfig/")
        page.wait_for_load_state("networkidle")

        h1 = page.locator("h1")
        expect(h1).to_have_count(1)
        # The h1 in module pages comes from the module docstring heading
        # LitConfig has "# LitConfig: A Test Module" as its first heading
        h1_text = h1.inner_text()
        assert "LitConfig" in h1_text, (
            f"Expected h1 to contain 'LitConfig', got '{h1_text}'"
        )
