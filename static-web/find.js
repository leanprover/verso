/**
 * Copyright (c) 2024 Lean FRO LLC. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 * Author: David Thrane Christiansen
 */

// Enable typescript
// @ts-check
/**
 * @type URLSearchParams
 */
let params = new URLSearchParams(document.location.search);
/**
 * @type string[]
 */
let domains = params.getAll("domain");
/**
 * @type string | null
 */
let paramName = params.get("name");

/**
 * @typedef {{id: string, address: string, data: any}} Item // Metadata for one particular item. The `data` depends on the domain.
 * @typedef {Record<string, Item[]>} DomainData // A mapping from canonical names to metadata. The array is usually a singleton.
 * @typedef {{title: string | null, description: string | null, contents: DomainData}} Domain
 * @typedef {Record<string, Domain>} XRef
 */

let xref = /** @type {{xref: XRef}} */ (/** @type {unknown} */ (window)).xref;

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

if (paramName) {
    /**
     * @type (Item & {domain: string})[]
     */
    let options = [];
    if (domains && domains.length > 0) {
        for (const i in domains) {
            let domain = domains[i];
            console.log("Considering domain " + domain);
            if (xref.hasOwnProperty(domain)) {
                console.log("Found domain " + domain);
                let opts = xref[domain];
                if (opts["contents"].hasOwnProperty(paramName)) {
                    options = opts["contents"][paramName].map((x) =>
                        Object.assign(x, { domain: domain }),
                    );
                }
            }
        }
    } else {
        for (const [dom, opts] of Object.entries(xref)) {
            if (opts["contents"].hasOwnProperty(paramName)) {
                for (const i of opts["contents"][paramName]) {
                    options.push(Object.assign(i, { domain: dom }));
                }
            }
        }
    }

    if (options.length == 0) {
        // Permalinks from before a bug fix that separated sections' HTML IDs from their
        // canonical names in the section domain were mangled as slugs. If we don't find
        // any results, we try to recover by checking equality modulo sluggification.
        // This workaround was introduced in August 2026 and should be removed when it
        // seems unlikely for old permalinks to be a significant problem.
        const nameSlug = sluggify(paramName);
        const searchDomains = domains && domains.length > 0 ? domains : Object.keys(xref);
        for (const domain of searchDomains) {
            if (!xref.hasOwnProperty(domain)) continue;
            const contents = xref[domain]["contents"];
            for (const key of Object.keys(contents)) {
                if (sluggify(key) === nameSlug) {
                    for (const i of contents[key]) {
                        options.push(Object.assign(i, { domain: domain }));
                    }
                }
            }
        }
    }

    if (options.length == 0) {
        addEventListener("DOMContentLoaded", (_event) => {
            document.title = "Not found: '" + paramName + "'";
            const titleElem = document.querySelector("#title");
            if (titleElem) {
                titleElem.innerHTML = "Not found: name '" + paramName + "'";
            }
            let allDomains = [];
            for (const d in xref) {
                allDomains.push(d);
            }
            if (domains.length < 1) {
                domains = allDomains;
            }
            const messageElem = document.querySelector("#message");
            if (messageElem) {
                messageElem.innerHTML = `
                    <p>Searched domains:</p>
                    <ul>
                        ${domains
                            .map((x) => `<li><code>${x}</code>: ${xref[x]["title"]}</li>`)
                            .join("")}
                    </ul>
                `;
            }
        });
    } else if (options.length == 1) {
        // Currently, our stored options look like absolute paths ('/Axiom').
        // This makes them relative ('Axiom') so that they will be set relative to the <base> tag
        const addr = new URL(options[0]["address"].replace(/^\//, ""), document.baseURI);
        addr.hash = options[0]["id"];
        window.location.replace(addr);
    } else {
        addEventListener("DOMContentLoaded", (_event) => {
            document.title = "Ambiguous: '" + paramName + "'";
            const titleElem = document.querySelector("#title");
            if (titleElem) {
                titleElem.innerHTML = "Ambiguous: name '" + paramName + "'";
            }
            const messageElem = document.querySelector("#message");
            if (messageElem) {
                messageElem.innerHTML = `
                    <p>Options:</p>
                    <ul>
                        ${options
                            .map(
                                (x, _idx) =>
                                    `<li>
                                <p>
                                    <a href="${x["address"] + "#" + x["id"]}">
                                        From ${xref[x["domain"]]["title"]}
                                    </a>
                                </p>
                            </li>`,
                            )
                            .join("\n")} +
                    </ul>
                `;
            }
        });
    }
} else {
    addEventListener("DOMContentLoaded", (_event) => {
        document.title = "No name provided";
        const titleElem = document.querySelector("#title");
        if (titleElem) {
            titleElem.innerHTML = "No name provided";
        }
        const messageElem = document.querySelector("#message");
        if (messageElem) {
            messageElem.innerHTML = `
                <p>This page expects a 'name' query parameter, along with documentation domains.</p>
            `;
        }
    });
}
