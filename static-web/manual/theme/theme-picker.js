/* Theme picker.
 *
 * Builds and mounts the dialog opened by `#theme-picker-button` (which is rendered
 * server-side as static HTML). Reads `window.versoThemes`, populates the dropdowns,
 * persists choices to localStorage, and live-previews on hover/focus. The inline head
 * script in `verso-themes.css`-paired no-flash block already set the initial theme;
 * this file only handles user interaction. */

(function () {
    "use strict";

    var data = window.versoThemes;
    if (!data || !Array.isArray(data.themes) || data.themes.length === 0) return;

    var button = document.getElementById("theme-picker-button");
    if (!button) return;

    // Graceful degradation: only one theme available -> hide the gear.
    if (data.themes.length < 2) {
        button.hidden = true;
        return;
    }

    function readMode() {
        try {
            return localStorage.getItem("verso-theme-mode");
        } catch (e) {
            return null;
        }
    }
    function writeMode(v) {
        try {
            if (v) localStorage.setItem("verso-theme-mode", v);
            else localStorage.removeItem("verso-theme-mode");
        } catch (e) {
            /* localStorage may be disabled — fall through */
        }
    }
    function readKey(k) {
        try {
            return localStorage.getItem(k);
        } catch (e) {
            return null;
        }
    }
    function writeKey(k, v) {
        try {
            if (v) localStorage.setItem(k, v);
            else localStorage.removeItem(k);
        } catch (e) {
            /* localStorage may be disabled */
        }
    }

    function applyTheme(id) {
        var t = data.themes.find(function (x) {
            return x.id === id;
        });
        if (!t) return;
        // Skip redundant attribute writes. `setAttribute` with the same value still fires
        // MutationObservers and any attribute-selector style recomputation, so a focus
        // preview that re-applies the already-visible theme would log as a spurious
        // "intermediate state" in tests and could trigger a wasteful style pass at runtime.
        var root = document.documentElement;
        if (root.getAttribute("data-verso-theme") !== id) {
            root.setAttribute("data-verso-theme", id);
        }
        if (root.getAttribute("data-verso-appearance") !== t.appearance) {
            root.setAttribute("data-verso-appearance", t.appearance);
        }
    }

    // The committed theme is whatever the no-flash script (or a previous picker commit)
    // actually applied to `<html>`. Reading the attribute matches what the user is currently
    // looking at — including the matchMedia result in auto mode — so Escape and outside-click
    // revert to the visible state instead of guessing from localStorage.
    function committedActiveId() {
        return document.documentElement.getAttribute("data-verso-theme");
    }

    var dialog = null;
    var trapHandlers = null;
    var lastFocus = null;
    // `trackedCommitted` is the id we should revert to when the dialog closes without a
    // commit. It is captured on `open()` (= the visible theme at that moment, which is the
    // last committed value since previews can only happen after open) and updated by `commit()`
    // so a subsequent dismiss/Escape/outside-click never undoes a real commit.
    var trackedCommitted = null;

    function buildDialog() {
        dialog = document.createElement("div");
        dialog.id = "theme-picker-dialog";
        dialog.setAttribute("role", "dialog");
        dialog.setAttribute("aria-label", "Theme picker");
        dialog.hidden = true;

        // Alphabetize by display name.
        var sortedThemes = data.themes.slice().sort(function (a, b) {
            return a.name.localeCompare(b.name);
        });
        var lightThemes = sortedThemes.filter(function (t) {
            return t.appearance === "light";
        });
        var darkThemes = sortedThemes.filter(function (t) {
            return t.appearance === "dark";
        });
        var hasMixed = lightThemes.length > 0 && darkThemes.length > 0;

        // "Match system" toggle, only when there's a mix of light and dark.
        var modeRow = document.createElement("div");
        modeRow.className = "theme-picker-row";
        var modeLabel = document.createElement("label");
        modeLabel.setAttribute("for", "theme-picker-mode");
        modeLabel.textContent = "Match system";
        var modeToggle = document.createElement("input");
        modeToggle.type = "checkbox";
        modeToggle.id = "theme-picker-mode";
        modeToggle.checked = (readMode() || "auto") === "auto";
        modeRow.appendChild(modeToggle);
        modeRow.appendChild(modeLabel);
        if (hasMixed) dialog.appendChild(modeRow);

        // Appearance-scoped defaults: a theme is "the default" relative to a given dropdown.
        // The light dropdown marks `defaultLight`; the dark dropdown marks `defaultDark`. The
        // single-mode dropdown marks `defaultSingle` — the theme an author chose for readers
        // who do not follow the system (either `defaultLight` or `defaultDark`, configured via
        // `defaultSingleAppearance` on `RenderConfig`).
        function isDefault(t, scope) {
            if (scope === "dark") return t.id === data.defaultDark;
            if (scope === "light") return t.id === data.defaultLight;
            return t.id === data.defaultSingle;
        }

        function makeSelect(id, labelText, items, selected, scope) {
            var row = document.createElement("div");
            row.className = "theme-picker-row";
            var l = document.createElement("label");
            l.setAttribute("for", id);
            l.textContent = labelText;
            var s = document.createElement("select");
            s.id = id;
            items.forEach(function (t) {
                var o = document.createElement("option");
                o.value = t.id;
                o.textContent = isDefault(t, scope) ? t.name + " (default)" : t.name;
                if (t.id === selected) o.selected = true;
                s.appendChild(o);
            });
            row.appendChild(l);
            row.appendChild(s);
            return { row: row, select: s };
        }

        var singleSel = makeSelect(
            "theme-picker-single",
            "Theme",
            sortedThemes,
            readKey("verso-theme-single") || data.defaultSingle,
            "single",
        );
        var lightSel = makeSelect(
            "theme-picker-light",
            "Light",
            lightThemes,
            readKey("verso-theme-light") || data.defaultLight,
            "light",
        );
        var darkSel = makeSelect(
            "theme-picker-dark",
            "Dark",
            darkThemes,
            readKey("verso-theme-dark") || data.defaultDark,
            "dark",
        );

        dialog.appendChild(singleSel.row);
        dialog.appendChild(lightSel.row);
        dialog.appendChild(darkSel.row);

        var preview = document.createElement("div");
        preview.id = "theme-picker-preview";
        preview.innerHTML = data.codeSample || "";
        dialog.appendChild(preview);

        // Per-theme metadata panel: description paragraph and source-link line. Rendered below
        // the code sample so the visual order is [chooser] [code sample] [about this theme].
        // Themes without description/sourceLink leave the panel empty (and hidden by CSS).
        var about = document.createElement("div");
        about.id = "theme-picker-about";
        var aboutDesc = document.createElement("p");
        aboutDesc.id = "theme-picker-description";
        var aboutLink = document.createElement("p");
        aboutLink.id = "theme-picker-source";
        var aboutLinkAnchor = document.createElement("a");
        aboutLinkAnchor.target = "_blank";
        aboutLinkAnchor.rel = "noopener noreferrer";
        aboutLink.appendChild(aboutLinkAnchor);
        about.appendChild(aboutDesc);
        about.appendChild(aboutLink);
        dialog.appendChild(about);

        function activeMetaTheme() {
            var prefersDark =
                window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches;
            var id;
            if (modeToggle.checked) {
                id = prefersDark ? darkSel.select.value : lightSel.select.value;
            } else {
                id = singleSel.select.value;
            }
            return data.themes.find(function (t) {
                return t.id === id;
            });
        }

        function refreshAbout() {
            var t = activeMetaTheme();
            if (!t) {
                about.hidden = true;
                return;
            }
            // Hide rows individually so a theme with only one of the two doesn't leave an
            // empty paragraph slot.
            if (t.description) {
                aboutDesc.textContent = t.description;
                aboutDesc.hidden = false;
            } else {
                aboutDesc.hidden = true;
                aboutDesc.textContent = "";
            }
            if (t.sourceLink && t.sourceLink.url && t.sourceLink.text) {
                aboutLinkAnchor.href = t.sourceLink.url;
                aboutLinkAnchor.textContent = t.sourceLink.text;
                aboutLink.hidden = false;
            } else {
                aboutLink.hidden = true;
                aboutLinkAnchor.removeAttribute("href");
                aboutLinkAnchor.textContent = "";
            }
            about.hidden = aboutDesc.hidden && aboutLink.hidden;
        }

        function refreshLayout() {
            var auto = modeToggle.checked;
            singleSel.row.hidden = auto;
            lightSel.row.hidden = !auto;
            darkSel.row.hidden = !auto;
            refreshAbout();
        }
        refreshLayout();

        // The auto-mode active theme is the dropdown that matches the current
        // `prefers-color-scheme`. Distinct from `committedActiveId()`, which reads the visible
        // `data-verso-theme` and is only meaningful for cancel/revert paths.
        function activeAutoThemeId() {
            var prefersDark =
                window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches;
            return prefersDark ? darkSel.select.value : lightSel.select.value;
        }

        function commit() {
            var newId;
            if (modeToggle.checked) {
                writeMode("auto");
                writeKey("verso-theme-light", lightSel.select.value);
                writeKey("verso-theme-dark", darkSel.select.value);
                newId = activeAutoThemeId();
            } else {
                writeMode("single");
                writeKey("verso-theme-single", singleSel.select.value);
                newId = singleSel.select.value;
            }
            applyTheme(newId);
            trackedCommitted = newId;
        }

        function previewTheme(id) {
            if (id) applyTheme(id);
        }

        modeToggle.addEventListener("change", function () {
            refreshLayout();
            commit();
        });
        [singleSel.select, lightSel.select, darkSel.select].forEach(function (sel) {
            sel.addEventListener("change", function () {
                commit();
                refreshAbout();
            });
            // No focus/hover preview: the picker commits immediately on `change`, so the
            // user already gets visible feedback when they pick an option. Firing a
            // preview on `focus` (or `mouseenter`) painted a stale "what's selected right
            // now in this dropdown" theme between the user opening the dropdown and
            // committing a new value — a perceivable mid-switch flash to the dropdown's
            // current default or to the opposite-mode theme. Escape and outside-click
            // still revert any in-flight preview, so a future re-introduction can hook
            // back in here once the preview-vs-commit semantics are stabilised.
        });

        document.body.appendChild(dialog);
    }

    function focusable() {
        return Array.from(
            dialog.querySelectorAll("select, input, button, [tabindex]:not([tabindex='-1'])"),
        ).filter(function (el) {
            return !el.hidden && !el.disabled;
        });
    }

    function trapTab(e) {
        if (e.key !== "Tab") return;
        var els = focusable();
        if (els.length === 0) return;
        var first = els[0],
            last = els[els.length - 1];
        if (e.shiftKey) {
            if (document.activeElement === first) {
                e.preventDefault();
                last.focus();
            }
        } else {
            if (document.activeElement === last) {
                e.preventDefault();
                first.focus();
            }
        }
    }

    function onEscape(e) {
        if (e.key === "Escape" && !dialog.hidden) close();
    }

    function open() {
        if (!dialog) buildDialog();
        lastFocus = document.activeElement;
        trackedCommitted = committedActiveId();
        dialog.hidden = false;
        button.setAttribute("aria-expanded", "true");
        var f = focusable();
        if (f.length) f[0].focus();
        trapHandlers = trapTab;
        dialog.addEventListener("keydown", trapHandlers);
        document.addEventListener("keydown", onEscape);
    }

    function close() {
        if (!dialog) return;
        // Every dismiss path (Escape, outside click, gear-toggle) routes through here. If the
        // user committed a choice, `trackedCommitted` is that choice; if they only previewed,
        // it's the state at open. Reapplying it unconditionally reverts hover/focus previews.
        if (trackedCommitted) applyTheme(trackedCommitted);
        dialog.hidden = true;
        button.setAttribute("aria-expanded", "false");
        if (trapHandlers) dialog.removeEventListener("keydown", trapHandlers);
        document.removeEventListener("keydown", onEscape);
        if (lastFocus && lastFocus.focus) lastFocus.focus();
    }

    button.addEventListener("click", function () {
        if (!dialog || dialog.hidden) open();
        else close();
    });

    // Dismiss when clicking outside.
    document.addEventListener("click", function (e) {
        if (!dialog || dialog.hidden) return;
        if (dialog.contains(e.target) || button.contains(e.target)) return;
        close();
    });
})();
