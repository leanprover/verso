/**
 * Copyright (c) 2024 Lean FRO LLC. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Author: David Thrane Christiansen
 */

// Enable typescript
// @ts-check

/**
 * @typedef {{id: string, address: string, data: unknown}} Item // Metadata for one particular item. The `data` depends on the domain.
 * @typedef {Record<string, Item[]>} DomainData // A mapping from canonical names to metadata. The array is usually a singleton.
 * @typedef {{title: string | null, description: string | null, contents: DomainData}} Domain
 * @typedef {Record<string, Domain>} XRef
 * @typedef {Item & {domain: string}} Option // An item together with the name of the domain that contains it.
 */

/**
 * The replacements for characters that are not valid in slugs. This mirrors the mangling table in
 * MultiVerso.Slug.
 * @type {Record<string, string>}
 */
const slugReplacements = {
    "<": "_LT_",
    ">": "_GT_",
    ";": "_SEMI_",
    "‹": "_FLQ_",
    "›": "_FRQ_",
    "«": "_FLQQ_",
    "»": "_FLQQ_",
    "⟨": "_LANGLE_",
    "⟩": "_RANGLE_",
    "(": "_LPAR_",
    ")": "_RPAR_",
    "[": "_LSQ_",
    "]": "_RSQ_",
    "→": "_ARR_",
    "↦": "_MAPSTO_",
    "⊢": "_VDASH_",
};

/**
 * Converts a string to a valid slug, mangling as appropriate. This mirrors the slug computation in
 * MultiVerso.Slug, so names can be compared with links that were minted from their slugs.
 * @param {string} s
 * @returns {string}
 */
function sluggify(s) {
    let out = "";
    for (const c of s) {
        if (/^[a-zA-Z0-9_-]$/.test(c)) out += c;
        else if (c === " " || c === "\t" || c === "\r" || c === "\n") out += "-";
        else out += slugReplacements[c] ?? "___";
    }
    return out;
}

/**
 * Creates an element whose children are the given nodes and strings.
 * @template {keyof HTMLElementTagNameMap} K
 * @param {K} tag
 * @param {...(Node | string)} children
 * @returns {HTMLElementTagNameMap[K]}
 */
function el(tag, ...children) {
    const elem = document.createElement(tag);
    elem.append(...children);
    return elem;
}

/**
 * Shows a heading and an explanatory message once the page has loaded.
 * @param {string} title
 * @param {...Node} message
 */
function show(title, ...message) {
    const render = () => {
        document.title = title;
        document.querySelector("#title")?.replaceChildren(title);
        document.querySelector("#message")?.replaceChildren(...message);
    };
    if (document.readyState === "loading") {
        addEventListener("DOMContentLoaded", render);
    } else {
        render();
    }
}

/**
 * Finds the items with the given name in the given domains. If there are none, then it finds the
 * items whose names have the same slug.
 * @param {XRef} xref
 * @param {string[]} domains
 * @param {string} name
 * @returns {Option[]}
 */
function lookup(xref, domains, name) {
    /** @type {Option[]} */
    const options = [];
    for (const domain of domains) {
        const items = xref[domain]?.contents;
        if (items && Object.hasOwn(items, name)) {
            for (const item of items[name] ?? []) {
                options.push({ ...item, domain });
            }
        }
    }
    if (options.length > 0) return options;

    // Permalinks from before a bug fix that separated sections' HTML IDs from their canonical names
    // in the section domain were mangled as slugs. The slug comparison recovers them. This
    // workaround was introduced in August 2026 and should be removed when it seems unlikely for old
    // permalinks to be a significant problem.
    const nameSlug = sluggify(name);
    for (const domain of domains) {
        const items = xref[domain]?.contents ?? {};
        for (const [key, keyItems] of Object.entries(items)) {
            if (sluggify(key) === nameSlug) {
                for (const item of keyItems) {
                    options.push({ ...item, domain });
                }
            }
        }
    }
    return options;
}

/**
 * Computes the URL of an item.
 *
 * Stored addresses look like absolute paths ('/Axiom'). The URL is relative to the `<base>` tag, so
 * the leading slash is removed.
 * @param {Option} option
 * @returns {URL}
 */
function optionUrl(option) {
    const root = typeof __versoSiteRoot !== "undefined" ? __versoSiteRoot : "";
    const url = new URL(option.address.replace(/^\//, ""), new URL(root, document.baseURI));
    url.hash = option.id;
    return url;
}

/**
 * Describes a domain by its title, falling back to its name.
 * @param {XRef} xref
 * @param {string} domain
 * @returns {(Node | string)[]}
 */
function describeDomain(xref, domain) {
    const title = xref[domain]?.title;
    return title ? [el("code", domain), ": ", title] : [el("code", domain)];
}

function main() {
    const params = new URLSearchParams(document.location.search);
    const name = params.get("name");
    const xref = /** @type {{xref?: XRef}} */ (/** @type {unknown} */ (window)).xref;

    if (!xref) {
        show(
            "Cross-reference data is unavailable",
            el(
                "p",
                "The cross-reference database for this site did not load, so no names can be found.",
            ),
        );
        return;
    }

    if (!name) {
        show(
            "No name provided",
            el(
                "p",
                "This page expects a ",
                el("code", "name"),
                " query parameter, along with documentation domains.",
            ),
        );
        return;
    }

    const requested = [...new Set(params.getAll("domain"))];
    const unknown = requested.filter((d) => !Object.hasOwn(xref, d));
    const domains =
        requested.length > 0 ? requested.filter((d) => Object.hasOwn(xref, d)) : Object.keys(xref);

    /** @type {Node[]} */
    const unknownNote =
        unknown.length > 0
            ? [
                  el(
                      "p",
                      unknown.length === 1
                          ? "This domain does not exist:"
                          : "These domains do not exist:",
                  ),
                  el("ul", ...unknown.map((d) => el("li", el("code", d)))),
              ]
            : [];

    const options = lookup(xref, domains, name);
    const [only] = options;

    if (only && options.length === 1) {
        window.location.replace(optionUrl(only));
    } else if (options.length === 0) {
        show(
            `Not found: '${name}'`,
            el("p", "The name ", el("code", name), " was not found."),
            ...unknownNote,
            ...(domains.length > 0
                ? [
                      el("p", "Searched domains:"),
                      el("ul", ...domains.map((d) => el("li", ...describeDomain(xref, d)))),
                  ]
                : [el("p", "No domains were searched.")]),
        );
    } else {
        show(
            `Ambiguous: '${name}'`,
            el("p", "The name ", el("code", name), " refers to more than one item. Options:"),
            el(
                "ul",
                ...options.map((option) => {
                    const link = el("a", "From ", ...describeDomain(xref, option.domain));
                    link.href = optionUrl(option).href;
                    return el("li", el("p", link));
                }),
            ),
            ...unknownNote,
        );
    }
}

main();
