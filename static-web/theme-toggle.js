// Theme toggle functionality with localStorage persistence
(function () {
    "use strict";

    const STORAGE_KEY = "verso-theme";

    // Get the system preference
    function getSystemTheme() {
        return window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
    }

    // Get the stored preference, or null if none
    function getStoredTheme() {
        try {
            return localStorage.getItem(STORAGE_KEY);
        } catch {
            return null;
        }
    }

    // Set the theme on the document
    function setTheme(theme) {
        if (theme === "system") {
            document.documentElement.removeAttribute("data-theme");
        } else {
            document.documentElement.setAttribute("data-theme", theme);
        }
        updateToggleIcon();
    }

    // Store the preference
    function storeTheme(theme) {
        try {
            if (theme === "system") {
                localStorage.removeItem(STORAGE_KEY);
            } else {
                localStorage.setItem(STORAGE_KEY, theme);
            }
        } catch {
            // localStorage might be unavailable
        }
    }

    // Get the effective (displayed) theme
    function getEffectiveTheme() {
        const stored = getStoredTheme();
        if (stored === "dark" || stored === "light") {
            return stored;
        }
        return getSystemTheme();
    }

    // Update the toggle button icon
    function updateToggleIcon() {
        const toggle = document.getElementById("theme-toggle");
        if (!toggle) return;

        const effective = getEffectiveTheme();
        // Show sun when dark (click to go light), moon when light (click to go dark)
        toggle.setAttribute(
            "aria-label",
            effective === "dark" ? "Switch to light mode" : "Switch to dark mode",
        );
        toggle.innerHTML = effective === "dark" ? "☀️" : "🌙";
    }

    // Cycle through: system -> dark -> light -> system
    function cycleTheme() {
        const stored = getStoredTheme();
        let newTheme;

        if (stored === null) {
            // Currently system preference - go to opposite of system
            newTheme = getSystemTheme() === "dark" ? "light" : "dark";
        } else if (stored === "dark") {
            newTheme = "light";
        } else {
            newTheme = "system";
        }

        storeTheme(newTheme);
        setTheme(newTheme);
    }

    // Initialize theme on page load
    function initTheme() {
        const stored = getStoredTheme();
        if (stored === "dark" || stored === "light") {
            setTheme(stored);
        }
        // If system preference, don't set data-theme (CSS handles it)
    }

    // Set up the toggle button click handler
    function initToggle() {
        const toggle = document.getElementById("theme-toggle");
        if (toggle) {
            toggle.addEventListener("click", cycleTheme);
            updateToggleIcon();
        }
    }

    // Listen for system theme changes
    function watchSystemTheme() {
        window.matchMedia("(prefers-color-scheme: dark)").addEventListener("change", () => {
            // Only update icon if using system preference
            if (!getStoredTheme()) {
                updateToggleIcon();
            }
        });
    }

    // Initialize immediately (before DOMContentLoaded) for theme to avoid flash
    initTheme();

    // Set up toggle and system watcher when DOM is ready
    if (document.readyState === "loading") {
        document.addEventListener("DOMContentLoaded", () => {
            initToggle();
            watchSystemTheme();
        });
    } else {
        initToggle();
        watchSystemTheme();
    }
})();
