from playwright.sync_api import expect, Page


class TestSearch:
    def test_searchbar(self, server: str, page: Page):
        """Test that the search box can find suggestions."""
        page.goto(f"{server}")

        page.get_by_role("searchbox").type("syntactic ASTs libraries extensions")
        expect(page.get_by_role("searchbox")).to_match_aria_snapshot(
            '- searchbox "Search": syntactic ASTs libraries extensions'
        )
        print(page.get_by_label("Results").aria_snapshot())
        expect(page.get_by_label("Results")).to_match_aria_snapshot(
            """
          - listbox "Results":
            - option "5. Output Formats …reduce the syntactic overhead of constructing ASTs. These libraries may also be used by authors of extensions to the Manual… Writing Documentation in Lean with Verso" [selected]:
              - link "5. Output Formats …reduce the syntactic overhead of constructing ASTs. These libraries may also be used by authors of extensions to the Manual… Writing Documentation in Lean with Verso":
                - paragraph:
                  - text: 5. Output Formats …reduce the
                  - emphasis: syntactic
                  - text: overhead of constructing
                  - emphasis: ASTs.
                  - text: These
                  - emphasis: libraries
                  - text: may also be used by authors of
                  - emphasis: extensions
                  - text: to the Manual…
                - paragraph: Writing Documentation in Lean with Verso
            - listitem: Showing 1/1 results""".strip()
        )

        page.get_by_role("searchbox").clear()
        page.get_by_role("searchbox").type("Html.rewritePo")
        expect(page.get_by_label("Results")).to_match_aria_snapshot(
            """
          - listbox "Results":
            - option "Lean.Html.rewritePostM Documentation" [selected]:
              - link "Lean.Html.rewritePostM Documentation":
                - paragraph:
                  - text: Lean.
                  - emphasis: Html.rewritePo
                  - text: stM
                - paragraph: Documentation
            - listitem: Showing 1/1 results""".strip()
        )

        page.get_by_role("searchbox").type("ndsville")
        expect(page.get_by_role("searchbox")).to_match_aria_snapshot(
            '- searchbox "Search": Html.rewritePondsville'
        )
        print(page.get_by_label("Results").aria_snapshot())
        expect(page.get_by_label("Results")).to_match_aria_snapshot(
            """
          - listbox "Results":
            - listitem: No results""".strip()
        )

    def test_unicode_input(self, server: str, page: Page):
        """Test that the search box converts Unicode abbreviations."""
        page.goto(f"{server}")

        searchbox = page.get_by_role("searchbox")
        # \alpha has longer completions (alphaphi), so eager replacement won't fire.
        # Press Tab to force replacement.
        searchbox.type("\\alpha")
        searchbox.press("Tab")
        expect(searchbox).to_match_aria_snapshot('- searchbox "Search": α')

        searchbox.clear()
        # Similarly \to has longer completions (\top etc.), so use Tab.
        searchbox.type("\\to")
        searchbox.press("Tab")
        expect(searchbox).to_match_aria_snapshot('- searchbox "Search": →')

    def test_suggestion(self, server: str, page: Page):
        """Test that the search box can find suggestions."""
        page.goto(f"{server}")
        page.get_by_role("searchbox").type("Html.none")
        expect(page.get_by_role("searchbox")).to_match_aria_snapshot(
            '- searchbox "Search": Html.none'
        )
        expect(page.get_by_label("Results")).to_match_aria_snapshot(
            """
          - listbox "Results":
            - option "Lean.Html.none ↪ Lean.Html.empty Suggestion" [selected]:
              - link "Lean.Html.none ↪ Lean.Html.empty Suggestion":
                - paragraph:
                  - text: Lean.
                  - emphasis: Html.none
                  - text: ↪ Lean.Html.empty
                - paragraph: Suggestion
            - listitem: Showing 1/1 results""".strip()
        )

        page.get_by_role("searchbox").press("Backspace")
        page.get_by_role("searchbox").press("Backspace")
        page.get_by_role("searchbox").press("Backspace")
        page.get_by_role("searchbox").type("il")
        expect(page.get_by_role("searchbox")).to_match_aria_snapshot(
            '- searchbox "Search": Html.nil'
        )
        expect(page.get_by_label("Results")).to_match_aria_snapshot(
            """
          - listbox "Results":
            - option "Lean.Html.nil ↪ Lean.Html.empty Suggestion" [selected]:
              - link "Lean.Html.nil ↪ Lean.Html.empty Suggestion":
                - paragraph:
                  - text: Lean.
                  - emphasis: Html.nil
                  - text: ↪ Lean.Html.empty
                - paragraph: Suggestion
            - listitem: Showing 1/1 results""".strip()
        )
