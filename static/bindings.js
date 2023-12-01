
window.onload = () => {
    for (const c of document.querySelectorAll(".hl.lean .token")) {
        if (c.dataset.binding != "") {
            c.addEventListener("mouseover", (event) => {
                for (const tok of c.closest(".hl.lean").querySelectorAll(".token")) {
                    if (c.dataset.binding == tok.dataset.binding) {
                        tok.classList.add("binding-hl");
                    }
                }
            });
        }
        c.addEventListener("mouseout", (event) => {
            for (const tok of c.closest(".hl.lean").querySelectorAll(".token")) {
                tok.classList.remove("binding-hl");
            }
        });

    }
}
