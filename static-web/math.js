// @ts-check

/**
 * Typesets the math elements inside `root` with KaTeX.
 * @param {ParentNode} root
 */
function versoRenderMath(root) {
    const katex =
        /** @type {{katex?: {render: (tex: string, elem: Element, opts: object) => void}}} */ (
            /** @type {unknown} */ (window)
        ).katex;
    if (!katex) return;
    for (const m of root.querySelectorAll(".math.inline")) {
        katex.render(m.textContent, m, { throwOnError: false, displayMode: false });
    }
    for (const m of root.querySelectorAll(".math.display")) {
        katex.render(m.textContent, m, { throwOnError: false, displayMode: true });
    }
}

document.addEventListener("DOMContentLoaded", () => versoRenderMath(document));
