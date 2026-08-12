/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 30, 0⟩
  breaking := true
  tag := "feat-full-page-search-interface"
  prs := [847]

#doc (Manual) "Full-Page Search Interface" =>

Add full-page search interface. There is a small {ref "feat-full-page-search-interface"}[breaking change] for custom domains with custom result formatting.

Pressing "Enter" in the search box now leads to a full-page search interface that shows more results with more context and includes checkboxes to filter the results by their semantic domain.
As a result, domains with custom search CSS should replace the `#search-wrapper` selector with the `.verso-search-results` class.
