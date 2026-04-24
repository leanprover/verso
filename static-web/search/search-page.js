/**
 * Copyright (c) 2026 Lean FRO LLC. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Author: David Thrane Christiansen
 */

// `domain-mappers.js` is emitted into the output directory at build time by the Lean
// genre's `emitSearchBox`, so it is not present in this source tree. That's also why
// `// @ts-check` is intentionally omitted: tsc's stricter JS pass would fail to resolve
// the import. The same pattern is used in `search-init.js`.

import { domainMappers, searchPriorities } from "./domain-mappers.js";
import { buildSearchableMap, computeCandidates, renderCandidateLi } from "./search-box.js";

const fuzzysort = /** @type {{fuzzysort: Fuzzysort.Fuzzysort}} */ (/** @type {unknown} */ (window))
    .fuzzysort;

/**
 * Lazy search state shared across renders. `xref.json` is fetched once, then reused for
 * every keystroke. Cached as a promise rather than a resolved value so a second call
 * arriving before the first `fetch` resolves joins the same in-flight request instead
 * of issuing a duplicate.
 * @type {null | Promise<{
 *   preparedData: Fuzzysort.Prepared[],
 *   mappedData: any,
 *   searchPriorities: any,
 *   docPriorities: Record<string, number>,
 *   searchIndex: any,
 * }>}
 */
let statePromise = null;

/**
 * True once `statePromise` has resolved. Used to suppress the "Searching…" placeholder
 * on post-load renders: once the index is in memory, each keystroke resolves on the next
 * microtask and flashing "Searching…" every time produces visible flicker.
 */
let stateReady = false;

const ensureState = () =>
    (statePromise ??= (async () => {
        const json = await fetch("xref.json").then((r) => r.json());
        const mappedData = buildSearchableMap(json, domainMappers);
        const preparedData = Object.keys(mappedData).map((name) => fuzzysort.prepare(name));
        const state = {
            preparedData,
            mappedData,
            searchPriorities: {
                semantic: searchPriorities?.semantic ?? 50,
                fullText: searchPriorities?.fullText ?? 50,
                domains: searchPriorities?.domains ?? {},
            },
            docPriorities: /** @type {any} */ (window).docPriorities ?? {},
            searchIndex: /** @type {any} */ (window).searchIndex,
        };
        stateReady = true;
        return state;
    })());

/**
 * Monotonic token: every call to `renderResultsFor` bumps it. The async render loop
 * checks the token after each `await` and bails if a newer render has started, so a
 * user who keeps typing doesn't see stale partial results appended to the list.
 */
let renderToken = 0;

/** Cached references to the count + list containers. */
let countEl = /** @type {HTMLParagraphElement | null} */ (null);
let listEl = /** @type {HTMLUListElement | null} */ (null);

/**
 * Active domain/fullText filter state. Initialized once, mutated in place as the user
 * toggles checkboxes; the render loop reads the current values on every pass.
 * @type {{ domains: Set<string>, fullText: boolean }}
 */
const filters = { domains: new Set(Object.keys(domainMappers)), fullText: true };

/**
 * Handles for every filter checkbox + its label so we can flip them to disabled/gray
 * when the current query has no hits in that bucket.
 * @type {{ fullText: null | {cb: HTMLInputElement, label: HTMLLabelElement},
 *          domains: Record<string, {cb: HTMLInputElement, label: HTMLLabelElement}> }}
 */
const filterElements = { fullText: null, domains: {} };

/**
 * Set the result-count text. Kept at the top of the results region regardless of which
 * render branch runs, so users always see the count (or the empty-state message).
 *
 * @param {string} text
 * @param {boolean} muted
 */
const setCount = (text, muted = false) => {
    if (!countEl) return;
    countEl.textContent = text;
    countEl.classList.toggle("muted", muted);
};

/**
 * Replace the results list with results for `query`. `""` shows the empty-state
 * placeholder and hides the list.
 *
 * @param {string} query
 */
const renderResultsFor = async (query) => {
    if (!countEl || !listEl) return;

    const myToken = ++renderToken;

    if (!query) {
        listEl.textContent = "";
        setCount("Type a query in the search box to see results.", true);
        clearFilterDisabled();
        return;
    }

    // Only show "Searching…" on the cold first render. After the index is in memory,
    // `ensureState()` resolves on the next microtask and the existing count would flash
    // to "Searching…" for a single frame on every keystroke.
    if (!stateReady) setCount("Searching…", true);
    const state = await ensureState();
    if (myToken !== renderToken) return;

    const allCandidates = computeCandidates(query, state);
    if (myToken !== renderToken) return;

    // Per-bucket counts over the unfiltered pool drive the "no results for this filter"
    // grayed-out state of each checkbox.
    const counts = { fullText: 0, domains: /** @type {Record<string, number>} */ ({}) };
    for (const c of allCandidates) {
        if (c.kind === "semantic") {
            const id = c.searchable.domainId;
            counts.domains[id] = (counts.domains[id] ?? 0) + 1;
        } else {
            counts.fullText++;
        }
    }
    updateFilterDisabled(counts);

    const candidates = allCandidates.filter((c) =>
        c.kind === "semantic" ? filters.domains.has(c.searchable.domainId) : filters.fullText,
    );

    const n = candidates.length;
    const total = allCandidates.length;
    if (n === total) {
        setCount(`${n} result${n === 1 ? "" : "s"}`);
    } else {
        setCount(`${n} of ${total} result${total === 1 ? "" : "s"}`);
    }

    listEl.textContent = "";
    if (n === 0) return;

    // The full-page view has room for wider snippets and more of them than the
    // cramped combobox dropdown does; these tune the per-result excerpt sizes.
    const textSnippet = { header: 60, content: 60, maxSnippets: 5 };

    // Render serially: full-text rendering awaits per-bucket loads, and serial order
    // preserves the computed ranking. Between each await we check the token so a newer
    // query abandons this render without corrupting the UI.
    //
    // Navigation is handled by the inner `<a class="search-result-link">` emitted by
    // `renderCandidateLi`, so no click listener is needed here. Middle-click,
    // open-in-new-tab, and keyboard Enter all work via the anchor's default behaviour.
    for (const candidate of candidates) {
        if (myToken !== renderToken) return;
        const li = await renderCandidateLi(candidate, {
            domainMappers,
            filter: query,
            document,
            textSnippet,
            asOption: false,
        });
        if (myToken !== renderToken) return;
        if (!li) continue;
        listEl.append(li);
    }
};

/**
 * Update the URL's `q` parameter in place without a page reload, so the address bar
 * reflects the currently displayed results (share/bookmark/back work).
 *
 * @param {string} query
 */
const syncUrl = (query) => {
    const url = new URL(window.location.href);
    if (query) {
        url.searchParams.set("q", query);
    } else {
        url.searchParams.delete("q");
    }
    window.history.replaceState(null, "", url.toString());
};

/**
 * Build the plain search input inside the host element. We use a native
 * `<input type="search">` (not the quick-jump combobox): the live-updating list below
 * is already showing every result, so a dropdown on top of it would be redundant.
 *
 * @param {HTMLElement} host
 * @param {string} initialValue
 * @return {HTMLInputElement}
 */
const mountInput = (host, initialValue) => {
    const input = document.createElement("input");
    input.type = "search";
    input.id = "search-page-input";
    input.className = "search-page-input";
    input.placeholder = "Search…";
    input.autocapitalize = "none";
    input.autocomplete = "off";
    input.spellcheck = false;
    input.setAttribute("aria-label", "Search");
    input.value = initialValue;
    host.append(input);
    return input;
};

let debounceTimer = 0;

/**
 * Build the filter checkboxes: one per known domain (label = the domain's `displayName`)
 * plus a trailing one for the full-text search stream. Toggling any box triggers an
 * in-place re-render of the current query.
 *
 * @param {HTMLElement} container
 * @param {() => string} readQuery  Returns the current input value so re-renders stay in sync.
 */
const mountFilters = (container, readQuery) => {
    const makeCheckbox = (labelText, initial, onChange) => {
        const label = document.createElement("label");
        label.className = "search-page-filter";
        const cb = document.createElement("input");
        cb.type = "checkbox";
        cb.checked = initial;
        cb.addEventListener("change", () => {
            onChange(cb.checked);
            renderResultsFor(readQuery());
        });
        label.append(cb, " ", labelText);
        container.append(label);
        return { cb, label };
    };

    // Full-text comes first (it's orthogonal to the domain-specific ones), then the
    // domains are sorted by display name so the ordering is stable across runs.
    filterElements.fullText = makeCheckbox("Full-text", filters.fullText, (checked) => {
        filters.fullText = checked;
    });
    const sortedDomains = Object.entries(domainMappers).sort(([, a], [, b]) =>
        a.displayName.localeCompare(b.displayName),
    );
    for (const [id, mapper] of sortedDomains) {
        filterElements.domains[id] = makeCheckbox(
            mapper.displayName,
            filters.domains.has(id),
            (checked) => {
                if (checked) filters.domains.add(id);
                else filters.domains.delete(id);
            },
        );
    }
};

/**
 * Gray out + disable any checkbox whose bucket has zero hits in the current (unfiltered)
 * candidate pool, so users don't waste a click on filters that would change nothing.
 * A box the user has already unchecked stays unchecked, but still gets disabled when
 * there's nothing to toggle it back onto.
 *
 * @param {{fullText: number, domains: Record<string, number>}} counts
 */
const updateFilterDisabled = (counts) => {
    const setState = (entry, count) => {
        if (!entry) return;
        const disabled = count === 0;
        entry.cb.disabled = disabled;
        entry.label.classList.toggle("search-page-filter--disabled", disabled);
    };
    setState(filterElements.fullText, counts.fullText);
    for (const id of Object.keys(filterElements.domains)) {
        setState(filterElements.domains[id], counts.domains[id] ?? 0);
    }
};

/** Reset all filter checkboxes to enabled (used when the query is empty). */
const clearFilterDisabled = () => {
    const clear = (entry) => {
        if (!entry) return;
        entry.cb.disabled = false;
        entry.label.classList.remove("search-page-filter--disabled");
    };
    clear(filterElements.fullText);
    for (const id of Object.keys(filterElements.domains)) clear(filterElements.domains[id]);
};

const init = async () => {
    const host = /** @type {HTMLElement | null} */ (document.querySelector(".search-page-host"));
    const resultsRoot = document.getElementById("search-page-results");
    if (!host || !resultsRoot) return;

    const initialQuery = new URLSearchParams(window.location.search).get("q")?.trim() ?? "";
    const input = mountInput(host, initialQuery);

    // Filter row lives between the input and the results, above the count, so users
    // see what's being narrowed before the count.
    const filtersEl = document.createElement("div");
    filtersEl.className = "search-page-filters";
    filtersEl.setAttribute("role", "group");
    filtersEl.setAttribute("aria-label", "Filter results");
    resultsRoot.append(filtersEl);
    mountFilters(filtersEl, () => input.value.trim());

    // Result count lives above the results list so it's visible even when the list is
    // short or empty. `aria-live="polite"` makes screen readers announce count changes
    // (e.g. "12 results") as the user types.
    countEl = document.createElement("p");
    countEl.id = "search-page-count";
    countEl.className = "search-page-count muted";
    countEl.setAttribute("aria-live", "polite");
    resultsRoot.append(countEl);

    // The shared `verso-search-results` class lets the domain-specific CSS (emitted
    // into `domain-display.css`) match here as well as inside the combobox. No
    // `role="listbox"`: results are navigated by tabbing through the `<a>` inside
    // each `<li>`, not via arrow-key selection with `aria-activedescendant`. A
    // listbox role without those semantics misleads assistive tech into announcing
    // a selectable set that doesn't exist.
    listEl = document.createElement("ul");
    listEl.className = "search-page-list verso-search-results";
    resultsRoot.append(listEl);

    await renderResultsFor(initialQuery);

    input.addEventListener("input", () => {
        const q = input.value.trim();
        syncUrl(q);
        if (debounceTimer) window.clearTimeout(debounceTimer);
        debounceTimer = window.setTimeout(() => {
            renderResultsFor(q);
        }, 120);
    });

    // Enter on a standalone input would submit a form if there were one; there isn't.
    // Live-update already covers typing, so just prevent any implicit form submission.
    input.addEventListener("keydown", (e) => {
        if (e.key === "Enter") e.preventDefault();
    });

    // Focus the input only when the page loaded without a query so the user can start
    // typing immediately. For direct links (`?q=foo`), leave focus alone so the user
    // can scroll and read results without fighting the browser for focus.
    if (!initialQuery) input.focus();
};

if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
} else {
    init();
}
