// Enable TypeScript checking.
// @ts-check

// Applies a saved table-of-contents width before the first paint.
//
// This is a tiny inline counterpart to toc-resize.js: it runs in the page head so that
// returning desktop readers do not see the default width flash to their saved width.
// It only records the width in the --verso-toc-user-width custom property; the
// stylesheet clamps it and ignores it on mobile, and toc-resize.js then takes over the
// interactive resizing. Keep the storage key in sync with toc-resize.js.

(function () {
    try {
        const saved = localStorage.getItem("verso-toc-width");
        // Parse to a number (as toc-resize.js does) and write that back, so a stored
        // value with stray whitespace becomes a valid length rather than `" 420 px"`.
        const width = saved === null ? NaN : Number(saved);
        if (Number.isFinite(width)) {
            document.documentElement.style.setProperty("--verso-toc-user-width", `${width}px`);
        }
    } catch (_) {
        // Leave the default width in place when local storage is unavailable.
    }
})();
