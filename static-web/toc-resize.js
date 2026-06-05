// Enable TypeScript checking.
// @ts-check

// Resizing of the table of contents.
//
// The page layout is determined entirely by CSS (see src/verso-manual/VersoManual/Html/Style.lean).
// This script only records the user's preferred width in the --verso-toc-user-width
// custom property and in localStorage. The stylesheet clamps that value to the
// viewport and decides when to honor it (desktop) or ignore it (mobile), so this file
// has no knowledge of the mobile breakpoint. On mobile the handle is `display: none`,
// so its pointer and keyboard listeners never fire there.
//
// A tiny inline script in the page head applies the saved width before first paint to
// avoid a flash of the default width; this file repeats that application defensively
// and wires up the interactive resizing.

(function () {
    const STORAGE_KEY = "verso-toc-width";
    // These bounds mirror the clamp() for --verso-toc-effective-width in Style.lean.
    // Keep them in sync.
    const MIN_WIDTH = 160;
    const MAX_WIDTH = 800;
    const MIN_MAIN_WIDTH = 320;
    const KEY_STEP = 16;
    const KEY_STEP_LARGE = 64;

    const handle = document.querySelector(".toc-resize-handle");
    const toc = document.getElementById("toc");
    if (!(handle instanceof HTMLElement) || !(toc instanceof HTMLElement)) return;

    function currentWidth() {
        return toc.getBoundingClientRect().width;
    }

    /**
     * The largest width the ToC can actually occupy at the current viewport size.
     * Mirrors the upper bound of the clamp() in Style.lean.
     * @returns {number}
     */
    function maxWidth() {
        return Math.max(MIN_WIDTH, Math.min(MAX_WIDTH, window.innerWidth - MIN_MAIN_WIDTH));
    }

    function syncAria() {
        handle.setAttribute("aria-valuenow", String(Math.round(currentWidth())));
        handle.setAttribute("aria-valuemax", String(Math.round(maxWidth())));
    }

    /**
     * Record a preferred ToC width. The stylesheet clamps it to the viewport, so this
     * only bounds the stored value to the absolute [MIN_WIDTH, MAX_WIDTH] range.
     * @param {number} width
     * @param {boolean} persist
     */
    function setWidth(width, persist) {
        const nextWidth = Math.round(Math.max(MIN_WIDTH, Math.min(MAX_WIDTH, width)));
        document.documentElement.style.setProperty("--verso-toc-user-width", `${nextWidth}px`);
        syncAria();
        if (persist) {
            try {
                localStorage.setItem(STORAGE_KEY, String(nextWidth));
            } catch (_) {
                // Some browsers can disable local storage while still allowing the page to run.
            }
        }
    }

    handle.setAttribute("role", "separator");
    handle.setAttribute("aria-orientation", "vertical");
    handle.setAttribute("aria-label", "Resize table of contents");
    handle.setAttribute("aria-valuemin", String(MIN_WIDTH));
    handle.tabIndex = 0;
    document.documentElement.classList.add("toc-resize-enabled");

    // Re-apply any saved width (the head script already did this before first paint).
    // The stylesheet ignores it on mobile.
    let saved = NaN;
    try {
        const savedValue = localStorage.getItem(STORAGE_KEY);
        if (savedValue !== null) {
            saved = Number(savedValue);
        }
    } catch (_) {
        // Leave the default width in place when local storage is unavailable.
    }
    if (Number.isFinite(saved)) {
        setWidth(saved, false);
    } else {
        syncAria();
    }

    // The stylesheet keeps the rendered width correct as the window changes; only the
    // reported ARIA range needs refreshing.
    window.addEventListener("resize", syncAria);

    /** @type {number | null} */
    let activePointer = null;
    let startX = 0;
    let startWidth = 0;

    /**
     * @param {PointerEvent} event
     */
    function startDrag(event) {
        activePointer = event.pointerId;
        startX = event.clientX;
        startWidth = currentWidth();
        handle.setPointerCapture(event.pointerId);
        handle.classList.add("dragging");
        document.body.style.userSelect = "none";
        document.body.style.cursor = "col-resize";
        event.preventDefault();
    }

    /**
     * @param {PointerEvent} event
     */
    function drag(event) {
        if (activePointer !== event.pointerId) return;
        setWidth(startWidth + event.clientX - startX, false);
    }

    /**
     * @param {PointerEvent} event
     */
    function stopDrag(event) {
        if (activePointer !== event.pointerId) return;
        activePointer = null;
        handle.releasePointerCapture(event.pointerId);
        handle.classList.remove("dragging");
        document.body.style.userSelect = "";
        document.body.style.cursor = "";
        setWidth(currentWidth(), true);
    }

    handle.addEventListener("pointerdown", startDrag);
    handle.addEventListener("pointermove", drag);
    handle.addEventListener("pointerup", stopDrag);
    handle.addEventListener("pointercancel", stopDrag);

    handle.addEventListener("keydown", (event) => {
        const step = event.shiftKey ? KEY_STEP_LARGE : KEY_STEP;
        switch (event.key) {
            case "ArrowLeft":
                setWidth(currentWidth() - step, true);
                event.preventDefault();
                break;
            case "ArrowRight":
                setWidth(currentWidth() + step, true);
                event.preventDefault();
                break;
            case "Home":
                setWidth(MIN_WIDTH, true);
                event.preventDefault();
                break;
            case "End":
                setWidth(maxWidth(), true);
                event.preventDefault();
                break;
        }
    });
})();
