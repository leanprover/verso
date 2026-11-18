window.onload = async () => {
    /**
     * @param {Element} tactic
     * @returns {HTMLInputElement | null}
     */
    function tacticToggle(tactic) {
        const toggle = tactic.querySelector(":scope > input.tactic-toggle");
        return toggle instanceof HTMLInputElement ? toggle : null;
    }

    // Don't show hovers inside of closed tactic states
    /** @param {Element} elem */
    function blockedByTactic(elem) {
        let parent = elem.parentElement;
        while (parent) {
            if (parent.classList.contains("tactic")) {
                const toggle = tacticToggle(parent);
                if (toggle) {
                    return !toggle.checked;
                }
            }
            parent = parent.parentElement;
        }
        return false;
    }

    // The innermost element under the pointer, used to show only the most specific hover
    /** @type {Element | null} */
    let hoverTarget = null;
    document.addEventListener(
        "mouseover",
        (e) => {
            hoverTarget = e.target instanceof Element ? e.target : null;
        },
        true,
    );

    // Visible tippy references; a tooltip is blocked while an unrelated one is visible
    /** @type {Set<HTMLElement>} */
    const visibleTippies = new Set();
    /** @param {Element} elem */
    function blockedByTippy(elem) {
        for (const ref of visibleTippies) {
            if (!ref.contains(elem) && !elem.contains(ref)) return true;
        }
        return false;
    }

    // Whether the element's tooltip would have content to show. Content nested in a
    // collapsed tactic region is covered by the region's proof-state tooltip, whether or
    // not a tippy instance is currently attached to it.
    /** @param {HTMLElement} el */
    function showsContent(el) {
        if (!el._tippy) return false;
        if (el.classList.contains("tactic")) {
            const toggle = tacticToggle(el);
            return !!toggle && !toggle.checked;
        }
        return (
            (!!el.querySelector(".hover-info") || "versoHover" in el.dataset) &&
            !blockedByTactic(el)
        );
    }

    // The nearest enclosing element whose tooltip has content
    /**
     * @param {Element | null} el
     * @returns {HTMLElement | null}
     */
    function innermostShowable(el) {
        while (el) {
            if (el instanceof HTMLElement && showsContent(el)) return el;
            el = el.parentElement;
        }
        return null;
    }

    // Binding highlights via event delegation with cached lookups
    /** @type {Map<string, Element[]>} */
    const bindingCache = new Map(); // context+binding -> [token elements]
    /** @type {Element[]} */
    let highlightedTokens = [];
    /**
     * @param {string | undefined} context
     * @param {string} binding
     */
    function getBindingTokens(context, binding) {
        const key = `${context}\0${binding}`;
        let tokens = bindingCache.get(key);
        if (!tokens) {
            tokens = [];
            for (const example of document.querySelectorAll(".hl.lean")) {
                if (example instanceof HTMLElement && example.dataset["leanContext"] === context) {
                    for (const tok of example.querySelectorAll(
                        `.token[data-binding="${CSS.escape(binding)}"]`,
                    )) {
                        tokens.push(tok);
                    }
                }
            }
            bindingCache.set(key, tokens);
        }
        return tokens;
    }
    /**
     * @param {Event} event
     * @returns {HTMLElement | null}
     */
    function eventToken(event) {
        const token = event.target instanceof Element ? event.target.closest(".token") : null;
        return token instanceof HTMLElement ? token : null;
    }
    for (const container of document.querySelectorAll(".hl.lean")) {
        if (!(container instanceof HTMLElement)) continue;
        container.addEventListener("mouseover", (event) => {
            const c = eventToken(event);
            const binding = c?.dataset["binding"];
            if (!c || !binding || !container.contains(c)) return;
            if (blockedByTactic(c)) return;
            const tokens = getBindingTokens(container.dataset["leanContext"], binding);
            for (const tok of tokens) {
                tok.classList.add("binding-hl");
            }
            highlightedTokens = tokens;
        });
        container.addEventListener("mouseout", (event) => {
            const c = eventToken(event);
            if (!c || !container.contains(c)) return;
            for (const tok of highlightedTokens) {
                tok.classList.remove("binding-hl");
            }
            highlightedTokens = [];
        });
    }
    // Add hovers
    const versoDocData = await window.versoLoadDocData();

    /** @param {Element} element */
    function hideParentTooltips(element) {
        let parent = element.parentElement;
        while (parent) {
            const tippyInstance = parent._tippy;
            if (tippyInstance) {
                tippyInstance.hide();
            }
            parent = parent.parentElement;
        }
    }

    /** @param {Element} element */
    function hideDescendantTooltips(element) {
        for (const ref of visibleTippies) {
            if (ref !== element && element.contains(ref)) {
                ref._tippy?.hide();
            }
        }
    }

    // Renders the documentation for a hover ID from the doc table
    /** @param {string} hoverId */
    function docHoverContent(hoverId) {
        const info = document.createElement("span");
        info.className = "hover-info";
        info.style.display = "block";
        const data = versoDocData[hoverId];
        if (data) {
            /* Verso generated the HTML from the Markdown at site build time. */
            const parsed = new DOMParser().parseFromString(data, "text/html");
            info.append(...parsed.body.childNodes);
            if (typeof versoRenderMath === "function") versoRenderMath(info);
        } else {
            info.textContent = `Failed to load doc ID: ${hoverId}`;
        }
        return info;
    }

    /** @type {TippyProps} */
    const defaultTippyProps = {
        /* theme: "lean", */
        maxWidth: "none",
        appendTo: () => document.body,
        interactive: true,
        delay: [100, null],
        /* ignoreAttributes: true, */
        followCursor: "initial",
        onShow(inst) {
            const ref = inst.reference;
            if (ref.className === "tactic") {
                const toggle = tacticToggle(ref);
                if (toggle && toggle.checked) {
                    return false;
                }
            } else if (ref.querySelector(".hover-info") || "versoHover" in ref.dataset) {
                if (blockedByTactic(ref)) {
                    return false;
                }
            } else {
                // Nothing to show here!
                return false;
            }
            // Show only the most specific hover under the pointer
            if (
                hoverTarget &&
                ref.contains(hoverTarget) &&
                innermostShowable(hoverTarget) !== ref
            ) {
                return false;
            }
            hideParentTooltips(ref);
            hideDescendantTooltips(ref);
            return !blockedByTippy(ref);
        },
        onShown(inst) {
            visibleTippies.add(inst.reference);
        },
        onHidden(inst) {
            visibleTippies.delete(inst.reference);
        },
        content(tgt) {
            const content = document.createElement("span");
            if (tgt.className === "tactic") {
                const state = tgt.querySelector(":scope > .tactic-state")?.cloneNode(true);
                if (state instanceof HTMLElement) {
                    state.style.display = "block";
                    content.appendChild(state);
                }
                content.style.display = "block";
                content.className = "hl lean popup";
            } else {
                content.className = "hl lean";
                content.style.display = "block";
                content.style.maxHeight = "300px";
                content.style.overflowY = "auto";
                content.style.overflowX = "hidden";
                // Messages come from the inline hover-info; documentation comes from the doc
                // table. An element with both (a message span sharing a documented token's
                // extent) shows both in one tooltip.
                const hoverId = tgt.dataset["versoHover"];
                const hoverInfo = tgt.querySelector(".hover-info");
                if (hoverInfo) {
                    content.appendChild(hoverInfo.cloneNode(true));
                }
                if (hoverId) {
                    content.appendChild(docHoverContent(hoverId));
                }
                if (hoverInfo && hoverId) {
                    content.classList.add("mixed");
                }
                const extraLinks =
                    tgt.dataset["versoLinks"] || tgt.parentElement?.dataset["versoLinks"];
                if (extraLinks) {
                    try {
                        /** @type {{href: string, long: string, short: string}[]} */
                        const extras = JSON.parse(extraLinks);
                        const links = document.createElement("ul");
                        links.className = "extra-doc-links";
                        extras.forEach((l) => {
                            const li = document.createElement("li");
                            const a = document.createElement("a");
                            a.href = l.href;
                            a.title = l.long;
                            a.textContent = l.short;
                            li.appendChild(a);
                            links.appendChild(li);
                        });
                        content.appendChild(links);
                    } catch (error) {
                        console.error(error);
                    }
                }
            }
            return content;
        },
    };

    document
        .querySelectorAll(
            ".hl.lean .const.token, .hl.lean .keyword.token, .hl.lean .literal.token, .hl.lean .option.token, .hl.lean .var.token, .hl.lean .typed.token, .hl.lean .level-var, .hl.lean .level-const, .hl.lean .level-op, .hl.lean .sort",
        )
        .forEach((element) => {
            element.setAttribute("data-tippy-theme", "lean");
        });
    document.querySelectorAll(".hl.lean .has-info.warning").forEach((element) => {
        element.setAttribute("data-tippy-theme", "warning message");
    });
    document.querySelectorAll(".hl.lean .has-info.information").forEach((element) => {
        element.setAttribute("data-tippy-theme", "info message");
    });
    document.querySelectorAll(".hl.lean .has-info.error").forEach((element) => {
        element.setAttribute("data-tippy-theme", "error message");
    });
    document.querySelectorAll(".hl.lean .tactic").forEach((element) => {
        element.setAttribute("data-tippy-theme", "tactic");
    });
    // Skip tokens inside closed tactics — they interfere with tactic tippys
    /** @type {Set<Element>} */
    const closedTactics = new Set();
    document.querySelectorAll(".hl.lean .tactic").forEach((tactic) => {
        const toggle = tacticToggle(tactic);
        if (toggle && !toggle.checked) closedTactics.add(tactic);
    });
    /** @param {Element} el */
    function isInsideClosedTactic(el) {
        const tactic = el.closest(".tactic");
        return tactic !== null && tactic !== el && closedTactics.has(tactic);
    }

    const tokenSelector =
        ".hl.lean .const.token, .hl.lean .keyword.token, .hl.lean .literal.token, .hl.lean .option.token, .hl.lean .var.token, .hl.lean .typed.token, .hl.lean .has-info, .hl.lean .tactic, .hl.lean .level-var, .hl.lean .level-const, .hl.lean .level-op, .hl.lean .sort";
    tippy(
        Array.from(document.querySelectorAll(tokenSelector)).filter(
            (el) => !isInsideClosedTactic(el),
        ),
        defaultTippyProps,
    );

    // Create/destroy token tippys when tactic checkbox toggles
    const tacticTippySelector =
        ".const.token, .keyword.token, .literal.token, .option.token, .var.token, .typed.token, .has-info, .level-var, .level-const, .level-op, .sort";
    document.querySelectorAll(".hl.lean .tactic").forEach((tactic) => {
        const toggle = tacticToggle(tactic);
        if (toggle)
            toggle.addEventListener("change", () => {
                if (toggle.checked) {
                    closedTactics.delete(tactic);
                    tactic.querySelectorAll(tacticTippySelector).forEach((el) => {
                        if (!el._tippy) {
                            tippy(el, defaultTippyProps);
                        }
                    });
                } else {
                    closedTactics.add(tactic);
                    tactic.querySelectorAll(tacticTippySelector).forEach((el) => {
                        if (el._tippy) el._tippy.destroy();
                    });
                }
                // The toggle changes which element's tooltip belongs to the pointer's position,
                // but the pointer stays put, so no hover event announces the change. Show the
                // right tooltip once the click that flipped the toggle has hidden the old one.
                setTimeout(() => {
                    if (hoverTarget && hoverTarget.isConnected) {
                        const showable = innermostShowable(hoverTarget);
                        if (showable && showable._tippy) showable._tippy.show();
                    }
                }, 0);
            });
    });
};
