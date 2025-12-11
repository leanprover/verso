/**
 * Copyright (c) 2024 Lean FRO LLC. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Author: Jakob Ambeck Vase
 *
 * This software or document includes material copied from or derived from https://www.w3.org/WAI/ARIA/apg/patterns/combobox/examples/combobox-autocomplete-both/.
 * Copyright © 2024 World Wide Web Consortium. https://www.w3.org/copyright/software-license-2023/
 */

// Enable typescript
// @ts-check

import { Range } from "./unicode-input.min.js";
import { InputAbbreviationRewriter } from "./unicode-input-component.min.js";

// Hacky way to import the fuzzysort library and get the types working. It's just `window.fuzzysort`.
const fuzzysort = /** @type {{fuzzysort: Fuzzysort.Fuzzysort}} */ (/** @type {unknown} */ (window))
    .fuzzysort;

const searchIndex = /** @type {{searchIndex: TextSearchIndex}} */ (/** @type {unknown} */ (window))
    .searchIndex;

/**
 * @typedef {{id: string, header: string, context: string, contents: string}} DocContent
 * @typedef {Promise<Record<number, DocContent>> & {resolve?: (data : any) => void}} DocContentPromise
 */
/**
 * @type {Record<string, DocContentPromise>}
 */
const docContents =
    /** @type {any} */ (window).docContents || /** @type {any} */ (window.docContents = {});

/** Whether to search word prefixes or whole words in full-text searches. Should match the setting in search-highlight.js.
 * @type {boolean}
 */
const expandMatches = true;

/**
 * Type definitions to help if you have typescript enabled.
 *
 * @typedef {{searchKey: string, address: string, domainId: string, ref?: any}} Searchable
 * @typedef {(domainData: any) => Searchable[]} DomainDataToSearchables
 * @typedef {{t: 'text', v: string} | {t: 'highlight', v: string}} MatchedPart
 * @typedef {(searchable: Searchable, matchedParts: MatchedPart[], document: Document) => HTMLElement} CustomResultRender
 * @typedef {{dataToSearchables: DomainDataToSearchables, customRender?: CustomResultRender, displayName: string, className: string}} DomainMapper
 * @typedef {Record<string, DomainMapper>} DomainMappers
 * @typedef {{ref: string, score: number, doc: DocContent}} TextMatch
 * @typedef {{item: Searchable, fuzzysortResult: Fuzzysort.Result, htmlItem: HTMLLIElement}|{terms: string, textItem: TextMatch, htmlItem: HTMLLIElement}} SearchResult
 * @typedef {{run: (tokens: string[]) => string[]}} ElasticLunrPipeline
 * @typedef {{bool?: "AND"|"OR", fields?:Record<string, {boost?: number}>, expand?: boolean}} SearchConfig
 * @typedef {{search: ((term: string, config: SearchConfig) => TextMatch[]), pipeline: ElasticLunrPipeline}|undefined|null} TextSearchIndex
 * @typedef {{original: string, stem: string, start: number, end: number}} TextToken
 * @typedef {{start: number, end: number, index: number, matches: TextToken[]}} TextSnippet
 */

/**
 * @param {TextSnippet} s1
 * @param {TextSnippet} s2
 * @return {number}
 */
const compareSnippets = (s1, s2) => {
    // First compare by number of unique terms
    let terms1 = new Set(s1.matches.map((x) => x.stem));
    let terms2 = new Set(s2.matches.map((x) => x.stem));
    let terms = terms1.size - terms2.size;
    if (terms !== 0) {
        return terms;
    }

    // Then by number of matches
    let matches = s1.matches.length - s2.matches.length;
    if (matches !== 0) {
        return matches;
    }

    // Finally by index
    return s1.index - s2.index;
};

/**
 * @param {string} text
 * @return {TextToken[]}
 */
const tokenizeText = (text) => {
    /** @type {TextToken[]} */
    const toks = [];
    const regex = /\S+/g;
    let match;
    while ((match = regex.exec(text)) !== null) {
        let stems = searchIndex.pipeline.run([match[0]]);
        for (const stem of stems) {
            toks.push({
                original: match[0],
                start: match.index,
                end: match.index + match[0].length,
                stem: stem.toLowerCase(),
            });
        }
    }
    return toks;
};

/**
 * @type {RegExp}
 */
const wordChar = /\p{L}/u;

/**
 * @param {string} text
 * @param {number} i
 * @return {number}
 */
const wordStartBefore = (text, i) => {
    while (i > 0) {
        if (!wordChar.test(text[i])) return i + 1; /* Adjust due to start indices being inclusive */
        i--;
    }
    return i;
};

/**
 * @param {string} text
 * @param {number} i
 * @return {number}
 */
const wordEndAfter = (text, i) => {
    while (i < text.length) {
        if (!wordChar.test(text[i]))
            return i; /* This is used as the (exclusive) end index in a slice, so one greater is correct */
        i++;
    }
    return i;
};

/**
 * @param {string} text
 * @param {string} query
 * @param {{contextLength?: number, maxSnippets?: number}} options
 * @return {Element|null}
 */
const highlightTextResult = (text, query, options = {}) => {
    const {
        contextLength = 50, // characters of context around each match
        maxSnippets = 3, // maximum number of snippets to return
    } = options;

    const terms = searchIndex.pipeline.run(
        query
            .trim()
            .toLowerCase()
            .split(/\s+/)
            .filter((term) => term.length > 0),
    );
    const toks = tokenizeText(text);
    const matches = expandMatches
        ? toks.filter((t) => terms.some((tm) => t.stem.startsWith(tm)))
        : toks.filter((t) => terms.includes(t.stem));

    if (matches.length === 0) {
        return null; // No matches found
    }

    // Group nearby matches into snippets
    /** @type {TextSnippet[]} */
    const snippets = [];
    let currentSnippet = null;
    for (const match of matches) {
        if (!currentSnippet || match.start > currentSnippet.end + contextLength * 2) {
            // Start new snippet
            currentSnippet = {
                start: wordStartBefore(text, Math.max(0, match.start - contextLength)),
                end: wordEndAfter(text, Math.min(text.length, match.end + contextLength)),
                index: snippets.length,
                matches: [match],
            };
            snippets.push(currentSnippet);
        } else {
            // Extend current snippet
            currentSnippet.end = wordEndAfter(
                text,
                Math.min(text.length, match.end + contextLength),
            );
            currentSnippet.matches.push(match);
        }
    }

    // Limit number of snippets. First, sort them by quality (which takes unique term occurrences and
    // total term count into consideration), then take the N best, then put them back in document order.
    const limitedSnippets = snippets
        .sort(compareSnippets)
        .slice(0, maxSnippets)
        .sort((s1, s2) => s1.index - s2.index);

    // Generate highlighted text for each snippet
    const highlightedSnippets = limitedSnippets.map((snippet) => {
        let snippetText = text.substring(snippet.start, snippet.end);

        // Adjust match positions relative to snippet start
        const relativeMatches = snippet.matches.map((match) => ({
            term: match.original,
            start: match.start - snippet.start,
            end: match.end - snippet.start,
        }));

        // Sort matches by position (descending) to avoid position shifts during replacement
        relativeMatches.sort((a, b) => b.start - a.start);

        // Apply highlighting
        for (const match of relativeMatches) {
            const before = snippetText.substring(0, match.start);
            const highlighted = `<em>${match.term}</em>`;
            const after = snippetText.substring(match.end);
            snippetText = before + highlighted + after;
        }

        // Add ellipses
        const prefix = snippet.start > 0 ? " …" : "";
        const suffix = snippet.end < text.length ? "… " : "";

        const elem = document.createElement("span");
        elem.appendChild(document.createTextNode(prefix));
        const m = document.createElement("span");
        m.innerHTML = snippetText;
        elem.appendChild(m);
        elem.appendChild(document.createTextNode(suffix));
        return elem;
    });

    const elem = document.createElement("span");
    elem.append(...highlightedSnippets);
    return elem;
};

/**
 * Maps data from Lean to an object with search terms as keys and a list of results as values.
 *
 * @param {any} json
 * @param {DomainMappers} domainMappers
 * @return {Record<string, Searchable[]>}
 */
const dataToSearchableMap = (json, domainMappers) =>
    Object.entries(json)
        .flatMap(([key, value]) =>
            key in domainMappers ? domainMappers[key].dataToSearchables(value) : undefined,
        )
        .reduce((acc, cur) => {
            if (cur == null) {
                return acc;
            }

            if (!acc.hasOwnProperty(cur.searchKey)) {
                acc[cur.searchKey] = [];
            }
            acc[cur.searchKey].push(cur);
            return acc;
        }, {});

/**
 * Maps from a data item to a HTML LI element
 *
 * @param {DomainMappers} domainMappers
 * @param {Searchable} searchable
 * @param {MatchedPart[]} matchedParts
 * @param {Document} document
 * @return {HTMLLIElement}
 */
const searchableToHtml = (domainMappers, searchable, matchedParts, document) => {
    const domainMapper = domainMappers[searchable.domainId];

    const li = document.createElement("li");
    li.role = "option";
    li.className = `search-result ${domainMapper.className}`;
    li.title = `${domainMapper.displayName} ${searchable.searchKey}`;

    if (domainMapper.customRender != null) {
        li.appendChild(domainMapper.customRender(searchable, matchedParts, document));
    } else {
        const searchTerm = document.createElement("p");
        for (const { t, v } of matchedParts) {
            if (t === "text") {
                searchTerm.append(v);
            } else {
                const emEl = document.createElement("em");
                searchTerm.append(emEl);
                emEl.textContent = v;
            }
        }
        li.appendChild(searchTerm);
    }

    const domainName = document.createElement("p");
    li.appendChild(domainName);
    domainName.className = "domain";
    domainName.textContent = domainMapper.displayName;

    return li;
};

/**
 * Gets the sort bucket for a given document ID.
 * @param {string} ref
 * @return {number}
 */
const docBucket = (ref) => {
    const utf8 = new TextEncoder().encode(ref);
    let hash = 0;
    for (let i = 0; i < utf8.length; i++) {
        hash = (hash + utf8[i]) % 256;
    }
    return hash;
};

/**
 * Loads the needed document bucket as a promise.
 * @param {string} ref
 * @return {Promise<Record<string, DocContent>>}
 */
const loadBucket = async (ref) => {
    const bucket = docBucket(ref);
    let bucketDocs = docContents[bucket];
    if (bucketDocs) {
        return bucketDocs;
    }

    /** @type {(data : any) => void} */
    let resolveFun;
    const promise = new Promise((resolve) => {
        resolveFun = resolve;
    });
    /** @type {any} */ (promise).resolve = resolveFun;
    docContents[bucket] = promise;
    const script = document.createElement("script");
    script.src = `-verso-search/searchIndex_${bucket}.js`;
    document.head.appendChild(script);

    return await docContents[bucket];
};

/**
 * @param {string} ref The identifier of the document to fetch from the store
 * @return {Promise<DocContent>}
 */
const getDocContents = async (ref) => {
    const resultBucket = await Promise.resolve(loadBucket(ref));

    /** @type {DocContent} */
    return resultBucket[ref];
};

/**
 * Maps from a data item to a HTML LI element
 * @param {string} term
 * @param {TextMatch} match
 * @param {Document} document
 * @return {Promise<HTMLLIElement|null>}
 */
const textResultToHtml = async (term, match, document) => {
    const doc = await getDocContents(match.ref);

    const li = document.createElement("li");
    li.role = "option";
    li.className = `search-result full-text`;
    li.title = "Full-text search result";
    // DEBUG:
    // li.title = `Full-text search result (${match.score}) (${match.ref})`;

    const searchTerm = document.createElement("p");
    let inHeader = true;
    let headerHl = highlightTextResult(doc.header, term, { contextLength: 30 }); // Only abbreviate huge headers
    if (!headerHl) {
        inHeader = false;
        headerHl = document.createElement("span");
        headerHl.append(document.createTextNode(doc.header));
    }
    headerHl.className = "header";
    searchTerm.append(headerHl);
    let contentHl = highlightTextResult(doc.contents, term, { contextLength: 10 });
    if (!contentHl) {
        if (!inHeader) {
            // Exclude this result. It'd be cleaner to do this elsewhere, but duplicating the string
            // processing would be expensive.
            return null;
        }
        contentHl = document.createElement("span");
        contentHl.appendChild(document.createTextNode("..."));
        for (const t of term.split(/\s+/)) {
            const tm = document.createElement("em");
            tm.appendChild(document.createTextNode(t));
            contentHl.appendChild(tm);
            contentHl.appendChild(document.createTextNode("..."));
        }
    }
    searchTerm.append(contentHl);
    li.appendChild(searchTerm);

    const domainName = document.createElement("p");
    li.appendChild(domainName);
    domainName.className = "domain";
    if (doc.context.trim() == "") {
        domainName.textContent = "Full-text search";
    } else {
        // This is a slight abuse of "domain", but it seems to work well
        let context = doc.context.replaceAll("\t", " » ");
        domainName.append(document.createTextNode(context));
        domainName.classList.add("text-context");
    }

    return li;
};

/**
 * @param {SearchResult} result
 * @returns string
 */
const resultToText = (result) => {
    if ("fuzzysortResult" in result) {
        return result.fuzzysortResult.target;
    } else {
        return result.terms;
    }
};

/**
 * @template T
 * @template Y
 * @param {T | null | undefined} v
 * @param {(t: T) => Y} fn
 * @returns Y | undefined
 */
const opt = (v, fn) => (v != null ? fn(v) : undefined);

/**
 * This is a modified version of the combobox at https://www.w3.org/WAI/ARIA/apg/patterns/combobox/examples/combobox-autocomplete-both/
 *
 * The license for the combobox is in `licenses.md`.
 */
class SearchBox {
    /**
     * @type {HTMLDivElement}
     */
    comboboxNode;

    /**
     * @type {HTMLButtonElement | null}
     */
    buttonNode;

    /**
     * @type {HTMLElement}
     */
    listboxNode;

    /**
     * @type {boolean}
     */
    comboboxHasVisualFocus;

    /**
     * @type {boolean}
     */
    listboxHasVisualFocus;

    /**
     * @type {boolean}
     */
    hasHover;

    /**
     * @type {SearchResult | null}
     */
    currentOption;

    /**
     * @type {SearchResult | null}
     */
    firstOption;

    /**
     * @type {SearchResult | null}
     */
    lastOption;

    /**
     * @type {SearchResult[]}
     */
    filteredOptions;

    /**
     * @type {string}
     */
    filter;

    /**
     * @type {Fuzzysort.Prepared[]}
     */
    preparedData;

    /**
     * Map from search term to list of results
     *
     * @type {Record<string, Searchable[]>}
     */
    mappedData;

    /** @type {HTMLLIElement} */
    noResultsElement = document.createElement("li");

    /** @type {HTMLLIElement[]} */
    domainFilters;

    /** @type {DomainMappers} */
    domainMappers;

    /** @type {InputAbbreviationRewriter} */
    imeRewriter;

    /**
     * @param {HTMLDivElement} comboboxNode
     * @param {HTMLButtonElement | null} buttonNode
     * @param {HTMLElement} listboxNode
     * @param {DomainMappers} domainMappers
     * @param {Record<string, Searchable[]>} mappedData
     */
    constructor(comboboxNode, buttonNode, listboxNode, domainMappers, mappedData) {
        this.comboboxNode = comboboxNode;
        this.buttonNode = buttonNode;
        this.listboxNode = listboxNode;
        this.domainMappers = domainMappers;
        this.mappedData = mappedData;
        this.preparedData = Object.keys(this.mappedData).map((name) => fuzzysort.prepare(name));

        // Add IME
        this.imeRewriter = new InputAbbreviationRewriter(
            {
                abbreviationCharacter: "\\",
                customTranslations: [],
                eagerReplacementEnabled: true,
            },
            comboboxNode,
        );

        // Initialize with a full-text result's query, if one is being presented
        const query = new URLSearchParams(window.location.search).get("terms")?.trim();
        comboboxNode.textContent = query ? query : "";

        this.comboboxHasVisualFocus = false;
        this.listboxHasVisualFocus = false;

        this.hasHover = false;

        this.currentOption = null;
        this.firstOption = null;
        this.lastOption = null;

        this.filteredOptions = [];
        this.filter = "";

        this.comboboxNode.addEventListener("keydown", this.onComboboxKeyDown.bind(this));
        this.comboboxNode.addEventListener("keyup", this.onComboboxKeyUp.bind(this));
        this.comboboxNode.addEventListener("click", this.onComboboxClick.bind(this));
        this.comboboxNode.addEventListener("focus", this.onComboboxFocus.bind(this));
        this.comboboxNode.addEventListener("blur", this.onComboboxBlur.bind(this));

        document.body.addEventListener("pointerup", this.onBackgroundPointerUp.bind(this), true);

        // initialize pop up menu

        this.listboxNode.addEventListener("pointerover", this.onListboxPointerover.bind(this));
        this.listboxNode.addEventListener("pointerout", this.onListboxPointerout.bind(this));

        this.domainFilters = [];
        const docDomainFilter = document.createElement("li");
        docDomainFilter.innerHTML = `<label><input type="checkbox" checked> Doc domain</label>`;
        docDomainFilter.classList.add("domain-filter");
        // TODO more work on the domain filters
        // this.domainFilters.push(docDomainFilter);

        // It's important not to call setValue with a blank string when query
        // is false, because that puts keyboard focus in the box.
        if (query) {
            this.setValue(query);
        }

        // Open Button

        const button = this.comboboxNode.nextElementSibling;

        if (button && button.tagName === "BUTTON") {
            button.addEventListener("click", this.onButtonClick.bind(this));
        }

        this.noResultsElement.textContent = "No results";
    }

    /**
     * @param {HTMLLIElement | null | undefined} option
     */
    setActiveDescendant(option) {
        if (option && this.listboxHasVisualFocus) {
            this.comboboxNode.setAttribute("aria-activedescendant", option.id);
            option.scrollIntoView({ behavior: "instant", block: "nearest" });
        } else {
            this.comboboxNode.setAttribute("aria-activedescendant", "");
        }
    }

    /**
     * @param {string} itemAddress
     * @param {string|null} query
     */
    confirmResult(itemAddress, query = null) {
        query = query ? "?terms=" + encodeURIComponent(query) : "";
        const [addr, id] = itemAddress.split("#", 2);
        itemAddress = id ? addr + query + "#" + id : addr + query;

        const base = document.querySelector("base");
        if (base) {
            let baseNoSlash = base.href.endsWith("/") ? base.href.slice(0, -1) : base.href;
            let itemAddressNoSlash = itemAddress.startsWith("/")
                ? itemAddress.slice(1)
                : itemAddress;
            window.location.assign(baseNoSlash + "/" + itemAddressNoSlash);
        } else {
            window.location.assign(itemAddress);
        }
    }

    /**
     * @param {string} value
     */
    setValue(value) {
        this.filter = value;
        this.comboboxNode.textContent = this.filter;
        this.imeRewriter.setSelections([new Range(this.filter.length, 0)]);
    }

    /**
     * @param {SearchResult} option
     */
    setOption(option) {
        if (option) {
            this.currentOption = option;
            this.setCurrentOptionStyle(this.currentOption);
            this.setActiveDescendant(this.currentOption.htmlItem);
        }
    }

    setVisualFocusCombobox() {
        this.listboxNode.classList.remove("focus");
        this.comboboxNode.parentElement?.classList.add("focus"); // set the focus class to the parent for easier styling
        this.comboboxHasVisualFocus = true;
        this.listboxHasVisualFocus = false;
        this.setActiveDescendant(null);
    }

    setVisualFocusListbox() {
        this.comboboxNode.parentElement?.classList.remove("focus");
        this.comboboxHasVisualFocus = false;
        this.listboxHasVisualFocus = true;
        this.listboxNode.classList.add("focus");
        this.setActiveDescendant(this.currentOption?.htmlItem);
    }

    removeVisualFocusAll() {
        this.comboboxNode.parentElement?.classList.remove("focus");
        this.comboboxHasVisualFocus = false;
        this.listboxHasVisualFocus = false;
        this.listboxNode.classList.remove("focus");
        this.currentOption = null;
        this.setActiveDescendant(null);
    }

    // ComboboxAutocomplete Events

    async filterOptions() {
        const currentOptionText = opt(this.currentOption, resultToText);
        const filter = this.filter;

        // Empty the listbox
        this.listboxNode.textContent = "";

        this.listboxNode.append(...this.domainFilters);

        if (filter.length === 0) {
            this.filteredOptions = [];
            this.firstOption = null;
            this.lastOption = null;
            this.currentOption = null;
            return null;
        }

        let results = fuzzysort.go(filter, this.preparedData, {
            limit: 30,
            threshold: 0.25,
        });

        const textResults = searchIndex
            ? searchIndex.search(filter, {
                  expand: expandMatches,
                  bool: "AND",
                  fields: {
                      header: { boost: 1.25 },
                      contents: { boost: 1 },
                      context: { boost: 0.1 },
                  },
              })
            : [];

        // Normalize the scores for text results by capping at a threshold, to better integrate with fuzzysearch results
        const bestPossibleText = 0.8;
        const maxTextScore = textResults.reduce(
            (max, item) => Math.max(max, item.score),
            -Infinity,
        );
        if (maxTextScore > bestPossibleText) {
            const factor = bestPossibleText / maxTextScore;
            for (const res of textResults) {
                res.score = res.score * factor;
            }
        }

        if (results.length === 0 && textResults.length === 0) {
            this.filteredOptions = [];
            this.firstOption = null;
            this.lastOption = null;
            this.currentOption = null;
            this.listboxNode.appendChild(this.noResultsElement);
            return null;
        }

        /**
         * @type {SearchResult|null}
         */
        let newCurrentOption = null;

        /** @type {(Fuzzysort.Result|TextMatch) []} */
        let allResults = [];
        allResults.push(...textResults);
        allResults.push(...results);
        allResults.sort((x, y) => y.score - x.score);
        allResults = allResults.slice(0, 30);

        this.filteredOptions = [];
        this.firstOption = null;
        this.lastOption = null;
        for (let i = 0; i < allResults.length; i++) {
            const result = allResults[i];
            if ("target" in result) {
                const dataItems = this.mappedData[result.target];
                for (let j = 0; j < dataItems.length; j++) {
                    const searchable = dataItems[j];
                    const option = searchableToHtml(
                        this.domainMappers,
                        dataItems[j],
                        result
                            .highlight((v) => ({ v }))
                            .map((v) =>
                                typeof v === "string"
                                    ? { t: "text", v }
                                    : { t: "highlight", v: v.v },
                            ),
                        document,
                    );
                    option.title = option.title; // DEBUG: show scores + ` (${result.score})`;
                    /** @type {SearchResult} */
                    const searchResult = {
                        item: searchable,
                        fuzzysortResult: result,
                        htmlItem: option,
                    };

                    option.addEventListener("click", this.onOptionClick(searchResult));
                    option.addEventListener("pointerover", this.onOptionPointerover.bind(this));
                    option.addEventListener("pointerout", this.onOptionPointerout.bind(this));
                    this.filteredOptions.push(searchResult);
                    this.listboxNode.appendChild(option);
                    if (i === 0 && j === 0) {
                        this.firstOption = searchResult;
                    }
                    if (i === allResults.length - 1 && j === dataItems.length - 1) {
                        this.lastOption = searchResult;
                    }
                    if (currentOptionText === resultToText(searchResult)) {
                        newCurrentOption = searchResult;
                    }
                }
            } else {
                const option = await textResultToHtml(filter, result, document);
                if (option) {
                    /** @type {SearchResult} */
                    const searchResult = {
                        terms: filter,
                        textItem: result,
                        htmlItem: option,
                    };
                    option.addEventListener("click", this.onOptionClick(searchResult));
                    option.addEventListener("pointerover", this.onOptionPointerover.bind(this));
                    option.addEventListener("pointerout", this.onOptionPointerout.bind(this));
                    this.filteredOptions.push(searchResult);
                    this.listboxNode.appendChild(option);
                    if (i === 0) {
                        this.firstOption = searchResult;
                    }
                    if (i === allResults.length - 1) {
                        this.lastOption = searchResult;
                    }
                    if (currentOptionText === resultToText(searchResult)) {
                        newCurrentOption = searchResult;
                    }
                }
            }
        }

        const moreResults = document.createElement("li");
        moreResults.textContent = `Showing ${allResults.length}/${results.total + textResults.length} results`;
        moreResults.className = `more-results`;
        this.listboxNode.appendChild(moreResults);

        if (newCurrentOption) {
            this.currentOption = newCurrentOption;
        }
        if (!this.currentOption) {
            this.currentOption = this.firstOption;
        }

        return newCurrentOption ?? this.firstOption;
    }

    /**
     * @param {SearchResult | null} option
     */
    setCurrentOptionStyle(option) {
        for (const opt of this.filteredOptions) {
            const el = opt.htmlItem;
            if (opt === option) {
                el.setAttribute("aria-selected", "true");
                if (
                    this.listboxNode.scrollTop + this.listboxNode.offsetHeight <
                    el.offsetTop + el.offsetHeight
                ) {
                    this.listboxNode.scrollTop =
                        el.offsetTop + el.offsetHeight - this.listboxNode.offsetHeight;
                } else if (this.listboxNode.scrollTop > el.offsetTop + 2) {
                    this.listboxNode.scrollTop = el.offsetTop;
                }
            } else {
                el.removeAttribute("aria-selected");
            }
        }
    }

    /**
     * @param {SearchResult} currentOption
     * @param {SearchResult} lastOption
     */
    getPreviousOption(currentOption, lastOption) {
        if (currentOption !== this.firstOption) {
            var index = this.filteredOptions.indexOf(currentOption);
            return this.filteredOptions[index - 1];
        }
        return lastOption;
    }

    /**
     * @param {SearchResult | null} currentOption
     * @param {SearchResult} firstOption
     */
    getNextOption(currentOption, firstOption) {
        if (currentOption != null && currentOption !== this.lastOption) {
            var index = this.filteredOptions.indexOf(currentOption);
            return this.filteredOptions[index + 1];
        }
        return firstOption;
    }

    /* MENU DISPLAY METHODS */

    doesOptionHaveFocus() {
        return this.comboboxNode.getAttribute("aria-activedescendant") !== "";
    }

    isOpen() {
        return this.listboxNode.style.display === "block";
    }

    isClosed() {
        return this.listboxNode.style.display !== "block";
    }

    open() {
        this.listboxNode.style.display = "block";
        this.comboboxNode.setAttribute("aria-expanded", "true");
        this.buttonNode?.setAttribute("aria-expanded", "true");
    }

    /**
     * @param {boolean} [force]
     */
    close(force) {
        if (
            force ||
            (!this.comboboxHasVisualFocus && !this.listboxHasVisualFocus && !this.hasHover)
        ) {
            this.setCurrentOptionStyle(null);
            this.listboxNode.style.display = "none";
            this.comboboxNode.setAttribute("aria-expanded", "false");
            this.buttonNode?.setAttribute("aria-expanded", "false");
            this.setActiveDescendant(null);
        }
    }

    /* combobox Events */

    /**
     * @param {KeyboardEvent} event
     * @returns void
     */
    async onComboboxKeyDown(event) {
        let eventHandled = false;
        const altKey = event.altKey;

        if (event.ctrlKey || event.shiftKey) {
            return;
        }

        switch (event.key) {
            case "Enter":
                if (this.listboxHasVisualFocus) {
                    this.setValue(opt(this.currentOption, resultToText) ?? "");
                    if (this.currentOption) {
                        if ("fuzzysortResult" in this.currentOption) {
                            this.confirmResult(this.currentOption.item.address);
                        } else {
                            const resultBucket = await Promise.resolve(
                                loadBucket(this.currentOption.textItem.ref),
                            );

                            /** @type {DocContent} */
                            const doc = resultBucket[this.currentOption.textItem.ref];

                            this.confirmResult(doc.id, this.currentOption.terms);
                        }
                    }
                }
                this.close(true);
                this.setVisualFocusCombobox();
                eventHandled = true;
                break;

            case "Down":
            case "ArrowDown":
                if (this.filteredOptions.length > 0 && this.firstOption != null) {
                    if (altKey) {
                        this.open();
                    } else {
                        this.open();
                        if (this.listboxHasVisualFocus) {
                            this.setOption(
                                this.getNextOption(this.currentOption, this.firstOption),
                            );
                            this.setVisualFocusListbox();
                        } else {
                            this.setOption(this.firstOption);
                            this.setVisualFocusListbox();
                        }
                    }
                }
                eventHandled = true;
                break;

            case "Up":
            case "ArrowUp":
                if (
                    this.filteredOptions.length > 0 &&
                    this.currentOption != null &&
                    this.lastOption != null
                ) {
                    if (this.listboxHasVisualFocus) {
                        this.setOption(this.getPreviousOption(this.currentOption, this.lastOption));
                    } else {
                        this.open();
                        if (!altKey) {
                            this.setOption(this.lastOption);
                            this.setVisualFocusListbox();
                        }
                    }
                }
                eventHandled = true;
                break;

            case "Esc":
            case "Escape":
                if (this.isOpen()) {
                    this.close(true);
                    this.filter = this.comboboxNode.textContent;
                    await this.filterOptions();
                    this.setVisualFocusCombobox();
                } else {
                    this.setValue("");
                    this.comboboxNode.textContent = "";
                }
                eventHandled = true;
                break;

            case "Tab":
                this.close(true);
                break;

            case "Home":
                this.imeRewriter.setSelections([new Range(0, 0)]);
                eventHandled = true;
                break;

            case "End":
                var length = this.comboboxNode.textContent.length;
                this.imeRewriter.setSelections([new Range(length, 0)]);
                eventHandled = true;
                break;

            default:
                break;
        }

        if (eventHandled) {
            event.stopImmediatePropagation();
            event.preventDefault();
        }
    }

    /**
     * @param {KeyboardEvent} event
     * @returns void
     */
    async onComboboxKeyUp(event) {
        let eventHandled = false;

        if (event.key === "Escape" || event.key === "Esc") {
            return;
        }

        switch (event.key) {
            case "Left":
            case "ArrowLeft":
            case "Right":
            case "ArrowRight":
            case "Home":
            case "End":
                this.setCurrentOptionStyle(null);
                this.setVisualFocusCombobox();
                eventHandled = true;
                break;

            default:
                if (this.comboboxNode.textContent !== this.filter) {
                    this.filter = this.comboboxNode.textContent;
                    this.setVisualFocusCombobox();
                    this.setCurrentOptionStyle(null);
                    eventHandled = true;
                    const option = await this.filterOptions();
                    if (option) {
                        if (this.isClosed() && this.comboboxNode.textContent.length) {
                            this.open();
                        }

                        this.setCurrentOptionStyle(option);
                        this.setOption(option);
                    } else {
                        this.close();
                        this.setActiveDescendant(null);
                    }
                }

                break;
        }

        if (eventHandled) {
            event.stopImmediatePropagation();
            event.preventDefault();
        }
    }

    onComboboxClick() {
        if (this.isOpen()) {
            this.close(true);
        } else {
            this.open();
        }
    }

    async onComboboxFocus() {
        this.filter = this.comboboxNode.textContent;
        await this.filterOptions();
        this.setVisualFocusCombobox();
        this.setCurrentOptionStyle(null);
    }

    onComboboxBlur() {
        this.removeVisualFocusAll();
        // Remove empty space created by browser after user deletes entered text.
        // Makes the placeholder appear again.
        if (this.comboboxNode.textContent.trim().length === 0) {
            this.comboboxNode.textContent = "";
        }
    }

    /**
     * @param {PointerEvent} event
     * @returns void
     */
    onBackgroundPointerUp(event) {
        const node = /** @type {Node | null} */ (event.target);
        if (
            !this.comboboxNode.contains(node) &&
            !this.listboxNode.contains(node) &&
            (this.buttonNode == null || !this.buttonNode.contains(node))
        ) {
            this.comboboxHasVisualFocus = false;
            this.setCurrentOptionStyle(null);
            this.removeVisualFocusAll();
            setTimeout(this.close.bind(this, true), 100);
        }
    }

    onButtonClick() {
        if (this.isOpen()) {
            this.close(true);
        } else {
            this.open();
        }
        this.comboboxNode.focus();
        this.setVisualFocusCombobox();
    }

    /* Listbox Events */

    onListboxPointerover() {
        this.hasHover = true;
    }

    onListboxPointerout() {
        this.hasHover = false;
        setTimeout(this.close.bind(this, false), 300);
    }

    // Listbox Option Events

    /**
     * @param {SearchResult} result
     * @returns MouseEventHandler
     */
    onOptionClick(result) {
        /**
         * @returns void
         */
        return async () => {
            this.comboboxNode.textContent = resultToText(result);
            if ("fuzzysortResult" in result) {
                this.confirmResult(result.item.address);
            } else {
                const resultBucket = await Promise.resolve(loadBucket(result.textItem.ref));

                /** @type {DocContent} */
                const doc = resultBucket[result.textItem.ref];

                this.confirmResult(doc.id, resultToText(result));
            }
            this.close(true);
        };
    }

    onOptionPointerover() {
        this.hasHover = true;
        this.open();
    }

    onOptionPointerout() {
        this.hasHover = false;
        setTimeout(this.close.bind(this, false), 300);
    }
}

/**
 * @typedef {{
 *   searchWrapper: HTMLElement;
 *   data: any;
 *   domainMappers: Record<string, DomainMapper>;
 * }} RegisterSearchArgs
 * @param {RegisterSearchArgs} args
 */
export const registerSearch = ({ searchWrapper, data, domainMappers }) => {
    const comboboxNode = /** @type {HTMLDivElement} */ (
        searchWrapper.querySelector("div[contenteditable]")
    );

    const buttonNode = searchWrapper.querySelector("button");
    const listboxNode = /** @type {HTMLElement | null} */ (
        searchWrapper.querySelector('[role="listbox"]')
    );
    if (comboboxNode != null && listboxNode != null) {
        new SearchBox(
            comboboxNode,
            buttonNode,
            listboxNode,
            domainMappers,
            dataToSearchableMap(data, domainMappers),
        );
    }
};
