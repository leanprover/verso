// Renders Verso's math with KaTeX.
//
// The work is confined to the wrappers that this release of Verso emits: an element belongs to the
// nearest enclosing element carrying `verso-content`, so a wrapper nested inside another wrapper is
// left to its own release's script. Each element is marked once it has been rendered, because KaTeX
// fed its own output produces visible garbage.
document.addEventListener("DOMContentLoaded", () => {
    for (const versoRoot of document.querySelectorAll("%%VERSO_WRAPPERS%%")) {
        renderAll(versoRoot, ".math.inline", false);
        renderAll(versoRoot, ".math.display", true);
    }

    function owns(versoRoot, el) {
        const owner = el.closest(".verso-content");
        return owner === versoRoot ||
            (owner === null && !(versoRoot.classList && versoRoot.classList.contains("verso-content")));
    }

    function renderAll(versoRoot, selector, displayMode) {
        for (const m of versoRoot.querySelectorAll(selector)) {
            if (!owns(versoRoot, m)) { continue; }
            if (m.dataset.versoMathRendered) { continue; }
            m.dataset.versoMathRendered = "true";
            katex.render(m.textContent, m, { throwOnError: false, displayMode: displayMode });
        }
    }
});
