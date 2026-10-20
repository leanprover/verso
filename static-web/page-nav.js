// Enable TypeScript checking.
// @ts-check

// Keyboard navigation between pages.
//
// The left and right arrow keys follow the previous and next links that `Toc.navButtons` (see
// src/verso-manual/VersoManual/Html.lean) marks with rel="prev" and rel="next". The keys are left
// alone when a modifier is held, so that browser shortcuts such as Alt+Left keep working, and
// when the focus is in an element that uses arrow keys itself, such as the search box. Elements
// that handle the keys themselves, such as the ToC resize handle, prevent the default action, and
// such events are ignored here.

(function () {
    /** @type {Record<string, string>} */
    const RELS = { ArrowLeft: "prev", ArrowRight: "next" };

    // Elements in which the arrow keys move a caret or change a value.
    const ARROW_KEY_ELEMENTS =
        "input, textarea, select, [contenteditable]:not([contenteditable='false']), " +
        "[role=textbox], [role=searchbox], [role=combobox], [role=listbox], [role=menu], " +
        "[role=slider], [role=separator], [role=tablist]";

    document.addEventListener("keydown", (event) => {
        if (event.defaultPrevented || event.repeat || event.isComposing) return;
        if (event.altKey || event.ctrlKey || event.metaKey || event.shiftKey) return;
        const rel = RELS[event.key];
        if (rel === undefined) return;
        const target = event.target;
        if (target instanceof Element && target.closest(ARROW_KEY_ELEMENTS)) return;
        const link = document.querySelector(`.prev-next-buttons a[rel="${rel}"]`);
        if (!(link instanceof HTMLAnchorElement)) return;
        event.preventDefault();
        link.click();
    });
})();
