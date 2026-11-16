/**
 * Copyright (c) 2024 Lean FRO LLC. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Author: David Thrane Christiansen
 */

// @ts-check

import { domainMappers, searchPriorities } from "./domain-mappers.js";
import { registerSearch } from "./search-box.js";

/** Whether the full-text search index was loaded before this module ran. */
const hasSearchIndex = Boolean(
    /** @type {{searchIndex?: unknown}} */ (/** @type {unknown} */ (window)).searchIndex,
);

// TODO: add the search box to the template
/**
 * Builds the search box itself.
 *
 * The `autocorrect` attribute is Safari-only. It is required to prevent autocorrect on iOS.
 * The `verso-search-results` class is shared with the full-page search results view so
 * domain-specific styling (written to `domain-display.css`) applies in both places.
 * @returns {HTMLDivElement}
 */
const buildSearchBox = () => {
    const input = document.createElement("div");
    input.id = "cb1-input";
    input.className = "cb_edit";
    input.setAttribute("contenteditable", "true");
    input.setAttribute("role", "searchbox");
    input.setAttribute("placeholder", hasSearchIndex ? "Search..." : "Jump to...");
    input.setAttribute("aria-autocomplete", "list");
    input.setAttribute("aria-expanded", "false");
    input.setAttribute("aria-controls", "cb1-listbox");
    input.setAttribute("aria-haspopup", "listbox");
    input.setAttribute("aria-label", "Search");
    input.setAttribute("spellcheck", "false");
    input.setAttribute("autocorrect", "false");
    input.setAttribute("autocapitalize", "none");
    input.setAttribute("inputmode", "search");

    const group = document.createElement("div");
    group.className = "group";
    group.append(input);

    const listbox = document.createElement("ul");
    listbox.id = "cb1-listbox";
    listbox.setAttribute("role", "listbox");
    listbox.setAttribute("aria-label", "Results");

    const combobox = document.createElement("div");
    combobox.className = "combobox combobox-list";
    combobox.append(group, listbox);

    const wrapper = document.createElement("div");
    wrapper.id = "search-wrapper";
    wrapper.className = "verso-search-results";
    wrapper.append(combobox);
    return wrapper;
};

// Initialize search box
const data = fetch("xref.json").then((data) => data.json());
window.addEventListener("load", () => {
    // Pages that render their own search UI (e.g. the full-page search results view,
    // which has a plain input next to live-updating results) opt out of the header
    // combobox entirely by declaring a `[data-search-host]` element. Those pages still
    // get access to the index data: they import `search-box.js`'s pure helpers
    // directly.
    if (document.querySelector("[data-search-host]")) return;
    const mount = document.querySelector("header");
    if (!mount) return;
    mount.append(buildSearchBox());
    const searchWrapper = document.querySelector(".combobox-list");
    if (!(searchWrapper instanceof HTMLElement)) return;
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
