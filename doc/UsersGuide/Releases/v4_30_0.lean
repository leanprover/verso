/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

open Verso.Genre Manual InlineLean


#doc (Manual) "Verso 4.30.0 (unreleased)" =>
%%%
tag := "release-v4.30.0"
file := "v4.30.0"
%%%

* Add support for custom prioritization of search results (#844)
* Add full-page search interface (#847). There is a small {ref "feat-full-page-search-interface"}[breaking change] for custom domains with custom result formatting.


# Search Result Prioritization
%%%
tag := none
%%%

This release gives authors the ability to affect search result ordering by assigning custom priorities.
Priorities may be assigned as follows:

* Semantic vs full-text results can be assigned overall priority levels.
* Semantic domains may be weighted, e.g. to boost all technical terms.
* Within a domain, items may be prioritized, e.g. to lower the priority of release notes relative to other text.
  This is done in JavaScript in the domain mapper.
* A genre may weight full-text results for parts based on part metadata.

In the {name}`Manual` genre, sections can be assigned search priority values using the metadata field {name}`Manual.PartMetadata.searchPriority`, which affects their full-text and semantic results, both for themselves and their children.

# Full-Page Search Interface
%%%
tag := "feat-full-page-search-interface"
%%%


Pressing "Enter" in the search box now leads to a full-page search interface that shows more results with more context and includes checkboxes to filter the results by their semantic domain.
As a result, domains with custom search CSS should repalce the `#search-wrapper` selector with the `.verso-search-results` class.
