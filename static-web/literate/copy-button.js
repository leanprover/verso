// Copy-to-clipboard for literate code boxes
(function () {
    "use strict";

    function addCopyButtons() {
        var codeBoxes = document.querySelectorAll(".code-box");
        for (var i = 0; i < codeBoxes.length; i++) {
            var box = codeBoxes[i];
            var button = document.createElement("button");
            button.className = "copy-button";
            button.textContent = "Copy";
            button.setAttribute("aria-label", "Copy code to clipboard");
            button.addEventListener("click", handleCopy);
            box.appendChild(button);
        }
    }

    function handleCopy(e) {
        var button = e.currentTarget;
        var codeBox = button.parentElement;
        // Collect text content from the code box, excluding the button itself
        var text = "";
        var children = codeBox.childNodes;
        for (var i = 0; i < children.length; i++) {
            var child = children[i];
            if (child !== button) {
                text += child.textContent;
            }
        }
        text = text.trim();

        if (navigator.clipboard && navigator.clipboard.writeText) {
            navigator.clipboard.writeText(text).then(function () {
                showCopied(button);
            });
        } else {
            // Fallback for older browsers
            var textarea = document.createElement("textarea");
            textarea.value = text;
            textarea.style.position = "fixed";
            textarea.style.opacity = "0";
            document.body.appendChild(textarea);
            textarea.select();
            try {
                document.execCommand("copy");
                showCopied(button);
            } catch (err) {
                // silently fail
            }
            document.body.removeChild(textarea);
        }
    }

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
