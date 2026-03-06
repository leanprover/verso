// Theme toggle functionality with localStorage persistence
(function () {
    "use strict";

    const STORAGE_KEY = "verso-theme";
    const THEMES = {
        system: { label: "System" },
        light: { label: "Light" },
        dark: { label: "Dark" },
    };
    const ICONS = {
        system: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" aria-hidden="true"><rect x="3.5" y="4.5" width="17" height="12" rx="2"></rect><path d="M8 19.5h8"></path><path d="M10 16.5v3"></path><path d="M14 16.5v3"></path></svg>',
        light: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" aria-hidden="true"><circle cx="12" cy="12" r="4"></circle><path d="M12 2.5v3"></path><path d="M12 18.5v3"></path><path d="M4.9 4.9l2.1 2.1"></path><path d="M17 17l2.1 2.1"></path><path d="M2.5 12h3"></path><path d="M18.5 12h3"></path><path d="M4.9 19.1 7 17"></path><path d="M17 7l2.1-2.1"></path></svg>',
        dark: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" aria-hidden="true"><path d="M21 13.2A8.8 8.8 0 1 1 10.8 3a7 7 0 0 0 10.2 10.2Z"></path></svg>',
        chevron:
            '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" aria-hidden="true"><path d="m7 10 5 5 5-5"></path></svg>',
    };

    let toggleButton = null;
    let toggleMenu = null;
    let optionButtons = [];

    function getSystemTheme() {
        return window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
    }

    function getStoredTheme() {
        try {
            const stored = localStorage.getItem(STORAGE_KEY);
            return stored === "dark" || stored === "light" ? stored : null;
        } catch {
            return null;
        }
    }

    function getSelectedTheme() {
        return getStoredTheme() ?? "system";
    }

    function getEffectiveTheme() {
        return getStoredTheme() ?? getSystemTheme();
    }

    function setTheme(theme) {
        if (theme === "system") {
            document.documentElement.removeAttribute("data-theme");
        } else {
            document.documentElement.setAttribute("data-theme", theme);
        }
        updateToggleUI();
    }

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

    function closeMenu() {
        if (!toggleButton || !toggleMenu) return;
        toggleMenu.hidden = true;
        toggleButton.setAttribute("aria-expanded", "false");
    }

    function openMenu() {
        if (!toggleButton || !toggleMenu) return;
        toggleMenu.hidden = false;
        toggleButton.setAttribute("aria-expanded", "true");
    }

    function applyTheme(theme) {
        storeTheme(theme);
        setTheme(theme);
        closeMenu();
    }

    function updateToggleUI() {
        const selectedTheme = getSelectedTheme();
        const effectiveTheme = getEffectiveTheme();

        if (toggleButton) {
            const icon = toggleButton.querySelector(".theme-toggle-button-icon");
            const chevron = toggleButton.querySelector(".theme-toggle-button-chevron");
            if (icon) icon.innerHTML = ICONS[selectedTheme];
            if (chevron) chevron.innerHTML = ICONS.chevron;

            const label =
                selectedTheme === "system"
                    ? `Theme: System (currently ${effectiveTheme})`
                    : `Theme: ${THEMES[selectedTheme].label}`;
            toggleButton.setAttribute("aria-label", label);
            toggleButton.title = label;
        }

        optionButtons.forEach((button) => {
            const optionTheme = button.getAttribute("data-theme-option");
            if (!optionTheme || !(optionTheme in THEMES)) return;

            const icon = button.querySelector(".theme-toggle-option-icon");
            if (icon) icon.innerHTML = ICONS[optionTheme];

            button.setAttribute("aria-checked", String(optionTheme === selectedTheme));
        });

        const systemMeta = document.querySelector(
            '[data-theme-option="system"] .theme-toggle-option-meta',
        );
        if (systemMeta) {
            systemMeta.textContent = `Follow your OS setting (currently ${effectiveTheme})`;
        }
    }

    function initTheme() {
        const stored = getStoredTheme();
        if (stored === "dark" || stored === "light") {
            document.documentElement.setAttribute("data-theme", stored);
        } else {
            document.documentElement.removeAttribute("data-theme");
        }
    }

    function initToggle() {
        const widget = document.getElementById("theme-toggle");
        toggleButton = document.getElementById("theme-toggle-button");
        toggleMenu = document.getElementById("theme-toggle-menu");
        optionButtons = Array.from(document.querySelectorAll("[data-theme-option]"));

        if (!toggleButton || !toggleMenu || optionButtons.length === 0) return;

        if (widget) {
            widget.hidden = false;
        }

        toggleButton.addEventListener("click", (event) => {
            event.preventDefault();
            event.stopPropagation();
            if (toggleMenu.hidden) {
                openMenu();
            } else {
                closeMenu();
            }
        });

        optionButtons.forEach((button) => {
            button.addEventListener("click", (event) => {
                event.stopPropagation();
                const optionTheme = event.currentTarget.getAttribute("data-theme-option");
                if (optionTheme === "system" || optionTheme === "light" || optionTheme === "dark") {
                    applyTheme(optionTheme);
                }
            });
        });

        document.addEventListener("click", (event) => {
            const widget = document.getElementById("theme-toggle");
            if (widget && event.target instanceof Node && !widget.contains(event.target)) {
                closeMenu();
            }
        });

        document.addEventListener("keydown", (event) => {
            if (event.key === "Escape") {
                closeMenu();
            }
        });

        updateToggleUI();
    }

    function watchSystemTheme() {
        const media = window.matchMedia("(prefers-color-scheme: dark)");
        const refresh = () => {
            if (!getStoredTheme()) {
                document.documentElement.removeAttribute("data-theme");
                updateToggleUI();
            }
        };

        if (typeof media.addEventListener === "function") {
            media.addEventListener("change", refresh);
        } else if (typeof media.addListener === "function") {
            media.addListener(refresh);
        }
    }

    initTheme();

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
