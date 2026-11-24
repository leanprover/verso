// @ts-check
/* global katex */
/// <reference path="../vendored-js/katex/katex.d.ts" />

/**
 * Typesets the math elements inside `root` with KaTeX.
 * @param {ParentNode} root
 */
function versoRenderMath(root) {
    if (typeof katex === "undefined") return;
    for (const m of /** @type {NodeListOf<HTMLElement>} */ (
        root.querySelectorAll(".math.inline")
    )) {
        katex.render(m.textContent, m, { throwOnError: false, displayMode: false });
    }
    for (const m of /** @type {NodeListOf<HTMLElement>} */ (
        root.querySelectorAll(".math.display")
    )) {
        katex.render(m.textContent, m, { throwOnError: false, displayMode: true });
    }
}

document.addEventListener("DOMContentLoaded", () => versoRenderMath(document));
