from playwright.sync_api import expect, Page

class TestSearch:
    def test_searchbar(self, server: str, page: Page):
        """Test that the search box can find suggestions."""
        page.goto(f"{server}") 

        page.get_by_role("searchbox").type("syntactic ASTs libraries extensions")
        expect(page.get_by_role("searchbox")).to_match_aria_snapshot('- searchbox "Search": syntactic ASTs libraries extensions')
        print(page.get_by_label("Results").aria_snapshot())
        expect(page.get_by_label("Results")).to_match_aria_snapshot("""
          - listbox "Results":
            - option "5. Output Formats …reduce the syntactic overhead of constructing ASTs. These libraries may also be used by authors of extensions to the Manual… Writing Documentation in Lean with Verso" [selected]:
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
            - listitem: Showing 1/1 results""".strip())

        page.get_by_role("searchbox").clear()
        page.get_by_role("searchbox").type("Html.visitM")
        expect(page.get_by_label("Results")).to_match_aria_snapshot("""
          - listbox "Results":
            - option "Verso.Output.Html.visitM Documentation" [selected]:
              - paragraph:
                - text: Verso.Output.
                - emphasis: Html.visitM
              - paragraph: Documentation
            - listitem: Showing 1/1 results""".strip())

        page.get_by_role("searchbox").type("onadsville")
        expect(page.get_by_role("searchbox")).to_match_aria_snapshot('- searchbox "Search": Html.visitMonadsville')
        print(page.get_by_label("Results").aria_snapshot())
        expect(page.get_by_label("Results")).to_match_aria_snapshot("""
          - listbox "Results":
            - listitem: No results""".strip())

    def test_suggestion(self, server: str, page: Page):
        """Test that the search box can find suggestions."""
        page.goto(f"{server}") 
        page.get_by_role("searchbox").type("Html.none")
        expect(page.get_by_role("searchbox")).to_match_aria_snapshot('- searchbox "Search": Html.none')
        expect(page.get_by_label("Results")).to_match_aria_snapshot("""- listbox "Results":
  - option "Html.none ↪ Verso.Output.Html.empty Suggestion" [selected]:
    - paragraph:
      - emphasis: Html.none
      - text: ↪ Verso.Output.Html.empty
    - paragraph: Suggestion
  - listitem: Showing 1/1 results""")

        page.get_by_role("searchbox").press("Backspace")
        page.get_by_role("searchbox").press("Backspace")
        page.get_by_role("searchbox").press("Backspace")
        page.get_by_role("searchbox").type("il")
        expect(page.get_by_role("searchbox")).to_match_aria_snapshot('- searchbox "Search": Html.nil')
        expect(page.get_by_label("Results")).to_match_aria_snapshot("""- listbox "Results":
  - listitem: No results""")
