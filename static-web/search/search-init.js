/**
 * Copyright (c) 2024 Lean FRO LLC. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Author: David Thrane Christiansen
 */

import { domainMappers } from "./domain-mappers.js";
import { registerSearch } from "./search-box.js";

// The search box itself. TODO: add to template
// autocorrect is a safari-only attribute. It is required to prevent autocorrect on iOS.
const searchHTML = `<div id="search-wrapper">
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
    const main = document.querySelector("header");
    main.insertAdjacentHTML("beforeend", searchHTML);
    const searchWrapper = document.querySelector(".combobox-list");
    data.then((data) => {
        registerSearch({ searchWrapper, data, domainMappers });
    });
});
