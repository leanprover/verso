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
  breaking := false
  tag := "search-priority"
  prs := [844]

#doc (Manual) "Search Result Prioritization" =>

Add support for custom prioritization of search results

This release gives authors the ability to affect search result ordering by assigning custom priorities.
Priorities may be assigned as follows:

* Semantic vs full-text results can be assigned overall priority levels.
* Semantic domains may be weighted, e.g. to boost all technical terms.
* Within a domain, items may be prioritized, e.g. to lower the priority of release notes relative to other text.
  This is done in JavaScript in the domain mapper.
* A genre may weight full-text results for parts based on part metadata.

In the {name}`Manual` genre, sections can be assigned search priority values using the metadata field {name}`Manual.PartMetadata.searchPriority`, which affects their full-text and semantic results, both for themselves and their children.
