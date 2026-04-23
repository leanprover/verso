/**
 * Copyright (c) 2024 Lean FRO LLC. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Author: David Thrane Christiansen
 */

import { domainMappers, searchPriorities } from "./domain-mappers.js";
import { registerSearch } from "./search-box.js";

// The search box itself. TODO: add to template
// autocorrect is a safari-only attribute. It is required to prevent autocorrect on iOS.
// The `verso-search-results` class is shared with the full-page search results view so
// domain-specific styling (emitted into `domain-display.css`) applies in both places.
const searchHTML = `<div id="search-wrapper" class="verso-search-results">
  <div class="combobox combobox-list">
    <div class="group">
      <div
        id="cb1-input"
        class="cb_edit"
        contenteditable="true"
        role="searchbox"
        placeholder="${window.searchIndex ? "Search..." : "Jump to..."}"
        aria-autocomplete="list"
        aria-expanded="false"
        aria-controls="cb1-listbox"
        aria-haspopup="listbox"
        aria-label="Search"
        spellcheck="false"
        autocorrect="false"
        autocapitalize="none"
        inputmode="search"
      ></div>
    </div>
    <ul id="cb1-listbox" role="listbox" aria-label="Results"></ul>
  </div>
</div>
`;

// Initialize search box
const data = fetch("xref.json").then((data) => data.json());
window.addEventListener("load", () => {
    // Pages that render their own search UI (e.g. the full-page search results view,
    // which has a plain input next to live-updating results) opt out of the header
    // combobox entirely by declaring a `[data-search-host]` element. Those pages still
    // get access to the index data — they import `search-box.js`'s pure helpers
    // directly.
    if (document.querySelector("[data-search-host]")) return;
    const mount = document.querySelector("header");
    if (!mount) return;
    mount.insertAdjacentHTML("beforeend", searchHTML);
    const searchWrapper = document.querySelector(".combobox-list");
    data.then((data) => {
        const windowAny = /** @type {any} */ (window);
        const docPriorities = windowAny.docPriorities;
        // Set by `search-config.js` (written by `emitSearchBox`) when the genre provides a
        // full-page search results view. Absent → Enter-without-selection stays a no-op.
        const searchPagePath =
            typeof windowAny.searchPagePath === "string" ? windowAny.searchPagePath : null;
        registerSearch({
            searchWrapper,
            data,
            domainMappers,
            searchPriorities,
            docPriorities,
            searchPagePath,
        });
    });
});
