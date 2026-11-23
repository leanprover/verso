(() => {
    const setupHover = () => {
        document.querySelectorAll(".marginalia-reference").forEach((reference) => {
            const noteId = reference.querySelector("[aria-details]")?.getAttribute("aria-details");
            const note = noteId ? document.getElementById(noteId) : null;
            if (!note) return;

            const highlight = () => {
                reference.classList.add("marginalia-highlight");
                note.classList.add("marginalia-highlight");
            };
            const unhighlight = () => {
                reference.classList.remove("marginalia-highlight");
                note.classList.remove("marginalia-highlight");
            };
            reference.addEventListener("pointerenter", highlight);
            reference.addEventListener("pointerleave", unhighlight);
            note.addEventListener("pointerenter", highlight);
            note.addEventListener("pointerleave", unhighlight);
        });
    };

    if (document.readyState === "loading") {
        document.addEventListener("DOMContentLoaded", setupHover, { once: true });
    } else {
        setupHover();
    }

    const mobile = matchMedia("(width <= 700px)");
    mobile.addEventListener("change", (event) => {
        if (!event.matches) {
            document.querySelectorAll(".marginalia-note:popover-open").forEach((note) => {
                if (note instanceof HTMLElement) note.hidePopover();
            });
        }
    });
})();
