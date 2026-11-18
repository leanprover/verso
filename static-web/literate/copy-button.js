// Copy-to-clipboard for literate code boxes
(function () {
    "use strict";

    function addCopyButtons() {
        for (const box of document.querySelectorAll(".code-box")) {
            const button = document.createElement("button");
            button.className = "copy-button";
            button.textContent = "Copy";
            button.setAttribute("aria-label", "Copy code to clipboard");
            button.addEventListener("click", () => handleCopy(button));
            box.appendChild(button);
        }
    }

    /** @param {HTMLButtonElement} button */
    function handleCopy(button) {
        const codeBox = button.parentElement;
        if (!codeBox) return;
        // Collect text content from the code box, excluding the button itself
        let text = "";
        for (const child of codeBox.childNodes) {
            const isOutput = child instanceof Element && child.classList.contains("lean-output");
            if (child !== button && !isOutput) {
                text += child.textContent;
            }
        }
        text = text.trim();

        if (navigator.clipboard && navigator.clipboard.writeText) {
            navigator.clipboard
                .writeText(text)
                .then(function () {
                    showCopied(button);
                })
                .catch(function () {
                    // clipboard write failed (e.g. permissions denied)
                });
        } else {
            // Fallback for older browsers
            const textarea = document.createElement("textarea");
            textarea.value = text;
            textarea.style.position = "fixed";
            textarea.style.opacity = "0";
            document.body.appendChild(textarea);
            textarea.select();
            try {
                document.execCommand("copy");
                showCopied(button);
            } catch {
                // silently fail
            }
            document.body.removeChild(textarea);
        }
    }

    /** @param {HTMLButtonElement} button */
    function showCopied(button) {
        button.textContent = "Copied!";
        button.classList.add("copied");
        setTimeout(function () {
            button.textContent = "Copy";
            button.classList.remove("copied");
        }, 2000);
    }

    if (document.readyState === "loading") {
        document.addEventListener("DOMContentLoaded", addCopyButtons);
    } else {
        addCopyButtons();
    }
})();
