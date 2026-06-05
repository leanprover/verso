// Enable TypeScript checking.
// @ts-check

(function () {
    const STORAGE_KEY = "verso-toc-width";
    const MIN_WIDTH = 160;
    const MAX_WIDTH = 800;
    const MIN_MAIN_WIDTH = 320;
    const MOBILE_QUERY = "(max-width: 700px)";
    const KEY_STEP = 16;
    const KEY_STEP_LARGE = 64;

    const handle = document.querySelector(".toc-resize-handle");
    const toc = document.getElementById("toc");
    if (!(handle instanceof HTMLElement) || !(toc instanceof HTMLElement)) return;

    const mobileMedia = window.matchMedia(MOBILE_QUERY);

    /** @type {number | null} */
    let preferredWidth = null;

    function maxWidth() {
        return Math.max(MIN_WIDTH, Math.min(MAX_WIDTH, window.innerWidth - MIN_MAIN_WIDTH));
    }

    /**
     * @param {number} width
     * @returns {number}
     */
    function clampWidth(width) {
        return Math.max(MIN_WIDTH, Math.min(maxWidth(), width));
    }

    /**
     * @param {number} width
     * @param {boolean} persist
     */
    function setWidth(width, persist) {
        const nextWidth = Math.round(clampWidth(width));
        document.documentElement.style.setProperty("--verso-toc-width", `${nextWidth}px`);
        handle.setAttribute("aria-valuenow", String(nextWidth));
        handle.setAttribute("aria-valuemax", String(maxWidth()));
        if (persist) {
            preferredWidth = nextWidth;
            try {
                localStorage.setItem(STORAGE_KEY, String(nextWidth));
            } catch (_) {
                // Some browsers can disable local storage while still allowing the page to run.
            }
        }
    }

    function currentWidth() {
        return toc.getBoundingClientRect().width;
    }

    function initializeWidth() {
        if (mobileMedia.matches) {
            preferredWidth = currentWidth();
            handle.setAttribute("aria-valuenow", String(Math.round(currentWidth())));
            handle.setAttribute("aria-valuemax", String(maxWidth()));
            return;
        }

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
            preferredWidth = saved;
            setWidth(saved, false);
        } else {
            preferredWidth = currentWidth();
            handle.setAttribute("aria-valuenow", String(Math.round(currentWidth())));
            handle.setAttribute("aria-valuemax", String(maxWidth()));
        }
    }

    handle.setAttribute("role", "separator");
    handle.setAttribute("aria-orientation", "vertical");
    handle.setAttribute("aria-label", "Resize table of contents");
    handle.setAttribute("aria-valuemin", String(MIN_WIDTH));
    handle.tabIndex = 0;
    document.documentElement.classList.add("toc-resize-enabled");
    initializeWidth();

    window.addEventListener("resize", () => {
        if (!mobileMedia.matches) {
            setWidth(preferredWidth ?? currentWidth(), false);
        } else {
            document.documentElement.style.removeProperty("--verso-toc-width");
        }
    });

    /** @type {number | null} */
    let activePointer = null;
    let startX = 0;
    let startWidth = 0;

    /**
     * @param {PointerEvent} event
     */
    function startDrag(event) {
        if (mobileMedia.matches) return;
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
        if (mobileMedia.matches) return;
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
