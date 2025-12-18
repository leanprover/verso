from playwright.sync_api import expect, Page

class TestSearch:
    def test_searchbar(self, server: str, page: Page):
        """Test that the search box can find suggestions."""
        page.goto(f"{server}") 

        page.get_by_role("searchbox").type("Verso provides genre authors with tools for generating HTML and TeX code via embedded languages")
        expect(page.get_by_role("searchbox")).to_match_aria_snapshot('- searchbox "Search": Verso provides genre authors with tools for generating HTML and TeX code via embedded languages')
        expect(page.get_by_label("Results")).to_match_aria_snapshot("""
          - listbox "Results":
            - option "5. Output Formats Verso provides genre authors with tools for generating HTML and TeX code via embedded languages that reduce… …be used by authors of extensions to the Manual genre, who need to… Writing Documentation in Lean with Verso" [selected]:
              - paragraph:
                - text: 5. Output Formats
                - emphasis: Verso
                - emphasis: provides
                - emphasis: genre
                - emphasis: authors
                - text: with
                - emphasis: tools
                - text: for
                - emphasis: generating
                - emphasis: HTML
                - text: and
                - emphasis: TeX
                - emphasis: code
                - emphasis: via
                - emphasis: embedded
                - emphasis: languages
                - text: that reduce… …be used by
                - emphasis: authors
                - text: of extensions to the Manual
                - emphasis: genre,
                - text: who need to…
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
