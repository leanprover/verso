document.addEventListener("DOMContentLoaded", () => {
    for (const m of document.querySelectorAll(".math.inline")) {
        katex.render(m.textContent, m, { throwOnError: false, displayMode: false });
    }
    for (const m of document.querySelectorAll(".math.display")) {
        katex.render(m.textContent, m, { throwOnError: false, displayMode: true });
    }
});
