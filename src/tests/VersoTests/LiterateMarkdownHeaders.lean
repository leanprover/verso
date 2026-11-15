/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Errata
import VersoLiterateCode
import Verso.Output.Html.Markdown

open Verso.Output.Html
open VersoLiterateCode

namespace VersoTests.LiterateMarkdownHeaders

/--
Renders Markdown module docs in sequence, as for the module docs on one page. Returns the HTML of
each and the levels of the page's table of contents entries.
-/
def renderModDocs (docs : List String) : List String × List Nat := Id.run <| StateT.run' (s := {}) do
  let mut out := []
  let mut levels := []
  for d in docs do
    let some md := Markdown.parse d
      | return (["parse failed"], [])
    let (html, hdgs) ← (md2Html md (trackHeadings := true) : StateM HeadingState _)
    out := out ++ [html.render]
    levels := levels ++ hdgs.toList.map (·.level)
  return (out, levels)

/--
info: (["<h2 id=\"Title\">Title</h2>", "<h3 id=\"Section\">Section</h3><h4 id=\"Detail\">Detail</h4>"], [1, 2, 3])
-/
#test_msgs in
#eval renderModDocs ["# Title", "## Section\n\n#### Detail"]

/-- info: (["<h2 id=\"A\">A</h2>", "<h2 id=\"B\">B</h2>"], [1, 1]) -/
#test_msgs in
#eval renderModDocs ["### A", "### B"]

/-- info: (["<h2 id=\"Title\">Title</h2>", "<h2 id=\"Title-1\">Title</h2>"], [1, 1]) -/
#test_msgs in
#eval renderModDocs ["# Title", "# Title"]
