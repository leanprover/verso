// @ts-check
import * as React from "react";
import * as ReactDOM from "react-dom";
import {
    EditorContext,
    EnvPosContext,
    Markdown,
    useEvent,
    useRpcSession,
} from "@leanprover/infoview";

const e = React.createElement;

// The last settled outcome of each test, keyed by its declaration and tagged with the source
// version that produced it. Leaving and returning to a test's `@[test]` marker shows its previous
// result again. The most recent RESULT_CACHE_LIMIT of them are held, each with the whole of its
// run's captured output.
const resultCache = new Map();
const RESULT_CACHE_LIMIT = 32;

// Records a test's outcome as the most recent, dropping the oldest to stay within the limit.
function cacheResult(declKey, entry) {
    resultCache.delete(declKey);
    resultCache.set(declKey, entry);
    while (resultCache.size > RESULT_CACHE_LIMIT) {
        resultCache.delete(resultCache.keys().next().value);
    }
}

// The editor theme's test-result colours, with fallbacks for a page outside VS Code. They are the
// colours of the theme's test icons, so they carry the verdict on the status glyph while the label
// beside it keeps the editor's text colour.
const STATUS_COLORS = {
    passed: "var(--vscode-testing-iconPassed, #2e7d32)",
    failed: "var(--vscode-testing-iconFailed, #c62828)",
    error: "var(--vscode-testing-iconErrored, #e65100)",
};

const STATUS_SYMBOLS = {
    passed: "✓",
    failed: "✗",
    error: "⚠",
};

const STATUS_LABELS = {
    passed: "Passed",
    failed: "FAILED",
    error: "ERROR",
};

const preStyle = {
    margin: "4px 0 0 0",
    padding: "6px 8px",
    whiteSpace: "pre-wrap",
    wordBreak: "break-word",
    background: "var(--vscode-textCodeBlock-background, rgba(127,127,127,0.1))",
    borderRadius: "3px",
    fontSize: "0.95em",
};

function formatDuration(ms) {
    if (ms < 1000) return ms + " ms";
    return (ms / 1000).toFixed(ms < 10000 ? 2 : 1) + " s";
}

function block(text) {
    return e("pre", { style: preStyle }, text);
}

function pad(n, w) {
    return String(n).padStart(w || 2, "0");
}

// The message of a rejected RPC call.
function errorMessage(err) {
    return (err && err.message) || String(err);
}

// How often a rejected `awaitOutput` is retried before the run is reported as failed, and the delay
// before each attempt. The InfoView replaces the RPC session as the cursor moves, which rejects the
// call in flight, so a rejection is part of the ordinary course of a run.
const AWAIT_RETRIES = 5;
const AWAIT_RETRY_MS = 200;

const monoFont = "var(--vscode-editor-font-family, monospace)";

// The editor theme's colour for secondary text: the badges, hints, and the output summary. The
// theme keeps it legible against the panel's background.
const dimColor = "var(--vscode-descriptionForeground, #717171)";

// The editor theme's colour for errors: a run that could not start, and a rejected seed.
const errorColor = "var(--vscode-errorForeground, #c62828)";

// The size of the text that accompanies a result rather than stating it: the badges, the hints, the
// durations, and the run settings. It is a fraction of the text around it, so the whole widget
// follows the editor's font size.
const dimSize = "0.9em";

// The time since `runStart`, an instant on the client's clock, ticking while mounted; shows zero
// until the start is known.
function Elapsed(props) {
    const runStart = props.runStart;
    const [elapsed, setElapsed] = React.useState(0);
    React.useEffect(
        function () {
            if (!runStart) return undefined;
            function update() {
                setElapsed(Math.max(0, Date.now() - runStart));
            }
            update();
            const timer = setInterval(update, 100);
            return function () {
                clearInterval(timer);
            };
        },
        [runStart],
    );
    return e("span", { style: { fontFamily: monoFont } }, formatDuration(elapsed));
}

// A fixed position against an element, aligned to its right edge and below it, going above it
// where the view has no room. The 48 pixels are the room a row of controls takes.
function placeUnder(anchor) {
    if (!anchor) return { display: "none" };
    const rect = anchor.getBoundingClientRect();
    const style = {
        position: "fixed",
        right: Math.max(8, window.innerWidth - rect.right),
        zIndex: 100,
    };
    if (rect.bottom + 48 > window.innerHeight) style.bottom = window.innerHeight - rect.top + 6;
    else style.top = rect.bottom + 6;
    return style;
}

// A popup anchored to an element, in the style of the InfoView's own menus. It is portalled to the
// document body, which puts it outside the disclosure summary that holds its anchor, so the
// controls inside it keep their own keyboard and pointer behaviour. It closes on Escape, on a
// click outside it, and when the view moves under it. `onClose` is told whether to return focus to
// the anchor.
function Popup(props) {
    const anchor = props.anchor;
    const ref = React.useRef(null);
    // Held in a ref, so the listeners are installed once rather than on every render around them.
    const onCloseRef = React.useRef(props.onClose);
    React.useEffect(function () {
        onCloseRef.current = props.onClose;
    });

    // Placed once, against the anchor as it stood when the popup opened.
    const [style] = React.useState(function () {
        return placeUnder(anchor);
    });

    React.useEffect(
        function () {
            function onPointerDown(ev) {
                if (ref.current && ref.current.contains(ev.target)) return;
                // A click on the anchor is its own toggle, which closes the popup in its turn.
                if (anchor && anchor.contains(ev.target)) return;
                onCloseRef.current(false);
            }
            function onKeyDown(ev) {
                if (ev.key !== "Escape") return;
                ev.stopPropagation();
                onCloseRef.current(true);
            }
            function onScroll(ev) {
                if (ref.current && ref.current.contains(ev.target)) return;
                onCloseRef.current(false);
            }
            function onResize() {
                onCloseRef.current(false);
            }
            document.addEventListener("pointerdown", onPointerDown, true);
            document.addEventListener("keydown", onKeyDown, true);
            window.addEventListener("scroll", onScroll, true);
            window.addEventListener("resize", onResize);
            return function () {
                document.removeEventListener("pointerdown", onPointerDown, true);
                document.removeEventListener("keydown", onKeyDown, true);
                window.removeEventListener("scroll", onScroll, true);
                window.removeEventListener("resize", onResize);
            };
        },
        [anchor],
    );

    return ReactDOM.createPortal(
        e(
            "div",
            { ref, className: "tooltip", style },
            e("div", { className: "tooltip-content" }, props.children),
        ),
        document.body,
    );
}

// A wall-clock time of day, rounded to the nearest second, from a Unix-epoch millisecond timestamp.
function formatClock(ms) {
    if (!ms) return "";
    const d = new Date(Math.round(ms / 1000) * 1000);
    return pad(d.getHours()) + ":" + pad(d.getMinutes()) + ":" + pad(d.getSeconds());
}

// A chunk's offset from the start of execution, in tenths of a second, as `(N.Ns)`.
function chunkOffset(c, execStartTime) {
    if (!execStartTime || !c.time) return "";
    return "(" + ((c.time - execStartTime) / 1000).toFixed(1) + "s)";
}

// A chunk's stream and offset as a plain string, for the native hover tooltip.
function chunkLabel(c, execStartTime) {
    const off = chunkOffset(c, execStartTime);
    return off ? c.stream + " " + off : c.stream;
}

// One output chunk in the editor's code font, italic for stderr, highlighted while hovered.
// Memoized, so a hover change re-renders only the two chunks whose highlight changes.
const ChunkSpan = React.memo(function ChunkSpan(props) {
    const c = props.chunk;
    return e(
        "span",
        {
            title: chunkLabel(c, props.execStartTime),
            onMouseEnter: function () {
                props.onHover(props.index);
            },
            style: {
                fontStyle: c.stream === "stderr" ? "italic" : undefined,
                borderRadius: "2px",
                backgroundColor: props.hovered
                    ? "var(--vscode-editor-hoverHighlightBackground, rgba(120,170,255,0.3))"
                    : undefined,
            },
        },
        c.text,
    );
});

// One chunk's span, at its position in the output.
function chunkSpan(chunks, i, execStartTime, hovered, setHovered) {
    return e(ChunkSpan, {
        key: i,
        index: i,
        chunk: chunks[i],
        execStartTime,
        hovered,
        onHover: setHovered,
    });
}

// Renders captured output: stdout and stderr interleaved in order. Hovering a chunk highlights it
// and reports its stream and time offset.
//
// The spans live in `cache` from one render to the next. A reply that adds output leaves the chunks
// already shown in place, so their spans are kept and only the new chunks get spans. Output that
// replaced what was shown, such as another run's, starts the spans over.
function outputBlock(cache, chunks, execStartTime, hovered, setHovered) {
    const c = cache.current;
    const grew =
        c.execStartTime === execStartTime &&
        c.spans.length > 0 &&
        c.spans.length <= chunks.length &&
        chunks[c.spans.length - 1] === c.last;
    if (!grew) {
        c.spans = [];
        c.execStartTime = execStartTime;
    }
    for (let i = c.spans.length; i < chunks.length; i++) {
        c.spans.push(chunkSpan(chunks, i, execStartTime, false, setHovered));
    }
    c.last = chunks.length ? chunks[chunks.length - 1] : null;
    // The highlight is the one thing the pointer decides, so it is the one span built again.
    const spans = c.spans.slice();
    if (hovered >= 0 && hovered < spans.length) {
        spans[hovered] = chunkSpan(chunks, hovered, execStartTime, true, setHovered);
    }
    return e(
        "pre",
        {
            style: { ...preStyle, fontFamily: monoFont },
            onMouseLeave: function () {
                setHovered(-1);
            },
        },
        spans,
    );
}

// The collapsible output disclosure: a summary naming the hovered chunk's stream and time offset,
// the interleaved chunks, and a copy button floating over the output, revealed on hover. The button
// copies `copy` when the caller gives it, which is how the test's own output shows alone while the
// button still offers the whole run's. Whether it is open belongs to the caller, so a collapse
// outlasts the output being replaced.
const OutputSection = React.memo(function OutputSection(props) {
    const chunks = props.chunks;
    const execStartTime = props.execStartTime;
    // The position of the output chunk under the cursor, highlighted with its timestamp shown, or
    // -1. A position keeps the highlight and the summary in step at any length of output.
    const [hovered, setHovered] = React.useState(-1);
    // The spans of the chunks, from one render to the next.
    const spanCache = React.useRef({ spans: [], last: null, execStartTime: 0 });
    // Whether a chunk of the output on show is under the pointer.
    const showing = hovered >= 0 && hovered < chunks.length;
    // Briefly true after the output is copied, to confirm the copy in the button label.
    const [copied, setCopied] = React.useState(false);
    // Whether the cursor is over the output area, revealing the floating copy button.
    const [over, setOver] = React.useState(false);
    // Whether the copy button has keyboard focus, which also reveals it.
    const [focused, setFocused] = React.useState(false);
    // The timer that ends the copy confirmation, so another copy restarts it in full.
    const copiedTimer = React.useRef(null);

    React.useEffect(function () {
        return function () {
            if (copiedTimer.current) clearTimeout(copiedTimer.current);
        };
    }, []);

    // Confirms a copy in the button's label for a moment.
    function confirmCopy() {
        setCopied(true);
        if (copiedTimer.current) clearTimeout(copiedTimer.current);
        copiedTimer.current = setTimeout(function () {
            copiedTimer.current = null;
            setCopied(false);
        }, 1500);
    }

    function copyOutput() {
        const text = (props.copy || chunks)
            .map(function (c) {
                return c.text;
            })
            .join("");
        if (navigator.clipboard && navigator.clipboard.writeText) {
            navigator.clipboard.writeText(text).then(confirmCopy, function () {});
            return;
        }
        // A page served outside a secure context copies from a selection instead, made in a field
        // held off the side of the view.
        const field = document.createElement("textarea");
        field.value = text;
        field.style.position = "fixed";
        field.style.opacity = "0";
        document.body.appendChild(field);
        field.select();
        try {
            if (document.execCommand("copy")) confirmCopy();
        } catch (err) {
            // The copy was refused, and the label stands as it is.
        } finally {
            document.body.removeChild(field);
        }
    }

    // The copy icon (two overlapping sheets), or a check mark once the output has been copied.
    const copyIcon = e(
        "svg",
        {
            width: 13,
            height: 13,
            viewBox: "0 0 24 24",
            fill: "none",
            stroke: "currentColor",
            strokeWidth: 2,
            strokeLinecap: "round",
            strokeLinejoin: "round",
        },
        copied
            ? e("path", { key: "check", d: "M20 6L9 17l-5-5" })
            : [
                  e("rect", { key: "sheet", x: 9, y: 9, width: 13, height: 13, rx: 2, ry: 2 }),
                  e("path", {
                      key: "back",
                      d: "M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1",
                  }),
              ],
    );

    // Revealed while the pointer is over the output or the button has keyboard focus.
    const copyButton = e(
        "button",
        {
            onClick: copyOutput,
            onFocus: function () {
                setFocused(true);
            },
            onBlur: function () {
                setFocused(false);
            },
            title: copied ? "Copied" : "Copy output to clipboard",
            "aria-label": "Copy output to clipboard",
            style: {
                position: "absolute",
                top: "4px",
                right: "4px",
                zIndex: 1,
                display: "flex",
                alignItems: "center",
                padding: "3px",
                lineHeight: 0,
                opacity: over || focused || copied ? 0.95 : 0,
                transition: "opacity 0.1s",
            },
        },
        copyIcon,
    );

    return e(
        "details",
        {
            open: props.open,
            onToggle: /** @param ev {React.ToggleEvent<HTMLDetailsElement>} */ function (ev) {
                props.onOpenChange(ev.currentTarget.open);
            },
            style: { marginTop: "4px" },
        },
        e(
            "summary",
            // The output of the test's own code is a peer of the named results below it, so its
            // line reads as they do.
            { style: { cursor: "pointer", lineHeight: 1.5 } },
            "Output",
            // The stream and offset of the chunk under the pointer hold their place in the line at
            // all times, the code font among them, so the line is the same height whether or not a
            // chunk is under the pointer and the output below stays where it is. The code font's
            // span holds a no-break space while there is nothing to name, which keeps the line box
            // it contributes.
            e(
                "span",
                {
                    style: {
                        color: dimColor,
                        fontSize: dimSize,
                        visibility: showing ? "visible" : "hidden",
                    },
                },
                "  —  ",
                e(
                    "span",
                    { style: { fontFamily: monoFont } },
                    showing ? chunks[hovered].stream : " ",
                ),
                " " + (showing ? chunkOffset(chunks[hovered], execStartTime) : ""),
            ),
        ),
        e(
            "div",
            {
                style: { position: "relative" },
                onMouseEnter: function () {
                    setOver(true);
                },
                onMouseLeave: function () {
                    setOver(false);
                },
            },
            copyButton,
            outputBlock(spanCache, chunks, execStartTime, hovered, setHovered),
        ),
    );
});

// The control that goes to the check a failure came from, as the InfoView's own sections offer a
// place: an icon at the right of the row that names the thing, with where it leads in its tooltip.
// An assertion records its own source position, which is where the control goes.
function sourceButton(source, reveal) {
    if (!source) return null;
    const file = decodeURIComponent((source.uri || "").split("/").pop() || "");
    const where = file + ":" + (source.startLine + 1) + ":" + source.startColumn;
    return e("button", {
        onClick: function () {
            reveal(source);
        },
        title: "Go to " + where,
        "aria-label": "Go to " + where,
        className: "link pointer dim mh2 codicon codicon-go-to-file",
        style: {
            background: "none",
            border: "none",
            padding: 0,
            color: "var(--vscode-textLink-foreground, #0078d4)",
        },
    });
}

// The button floated to the right of a result's own row. A click there is the control's own, so it
// leaves the disclosure as it was.
function sourceControl(source, reveal) {
    const button = sourceButton(source, reveal);
    if (!button) return null;
    return e(
        "span",
        {
            className: "fr",
            onClick: function (ev) {
                ev.preventDefault();
            },
        },
        button,
    );
}

// A result that reveals something is a disclosure, and the browser draws its triangle. A result
// with nothing to reveal is a row of the same shape whose marker is there but invisible, so the
// names of the results in a tree line up whether or not they open.
const treeStyle =
    ".errata-leaf { display: list-item; list-style: disclosure-closed inside }\n" +
    ".errata-leaf::marker { color: transparent }";

// One named result in the tree: its verdict, its name, and how long its own code took. A result
// that reported something opens to show it, in the order a reader wants it: why it did not pass,
// what its own code wrote, then the named results inside it. A result that reported nothing beyond
// its verdict is a row of its own, with no triangle to open.
function NamedResult(props) {
    const result = props.results[props.id];
    // This result's own spans, and the chunk of them under the cursor.
    const spanCache = React.useRef({ spans: [], last: null, execStartTime: 0 });
    const [hovered, setHovered] = React.useState(-1);
    const inside = props.kids[props.id] || [];
    const reported = !!(result.message || result.detail || result.output.length || inside.length);
    const open = reported && props.isOpen(props.id);
    // A result reads as the panel's own text, so its rows take the size around them and the tree
    // stays legible at any editor font. Nesting adds no size of its own, so a result at any depth
    // reads the same.
    const rowStyle = { marginTop: "2px" };
    const row = [
        e(
            "span",
            {
                key: "status",
                role: "img",
                "aria-label": STATUS_LABELS[result.status] || "Running",
                style: { color: STATUS_COLORS[result.status] || dimColor, fontWeight: 600 },
            },
            STATUS_SYMBOLS[result.status] || "…",
        ),
        " " + (result.name || "result"),
        result.durationMs
            ? e(
                  "span",
                  { key: "duration", style: { color: dimColor, fontSize: dimSize } },
                  "  " + formatDuration(result.durationMs),
              )
            : null,
        sourceControl(result.location, props.reveal),
    ];

    if (!reported) return e("div", { className: "errata-leaf", style: rowStyle }, ...row);

    return e(
        "details",
        {
            open,
            onToggle: /** @param ev {React.ToggleEvent<HTMLDetailsElement>} */ function (ev) {
                props.onOpenChange(props.id, ev.currentTarget.open);
            },
            style: { marginTop: "2px" },
        },
        e("summary", { style: { ...rowStyle, marginTop: 0, cursor: "pointer" } }, ...row),
        open
            ? e(
                  "div",
                  { style: { marginLeft: "1em" } },
                  result.message ? block(result.message) : null,
                  result.detail ? block(result.detail) : null,
                  result.output.length
                      ? outputBlock(
                            spanCache,
                            result.output,
                            props.execStartTime,
                            hovered,
                            setHovered,
                        )
                      : null,
                  inside.map(function (id) {
                      return e(NamedResult, { ...props, key: id, id });
                  }),
              )
            : null,
    );
}

/**
 * @typedef {"passed" | "failed" | "error"} Status the verdict of a result, as Lean reports it
 * @typedef {Status | ""} ShownStatus a verdict, or blank while a result is still running
 * @typedef {{uri: string, startLine: number, startColumn: number, endLine: number,
 *            endColumn: number}} Source the span of a failed check
 * @typedef {{stream: string, text: string, time?: number, result?: number}} Chunk
 * @typedef {{id: number, parent: number, name: string, status: ShownStatus, durationMs: number,
 *            message: string, detail: string, location: Source | null,
 *            output: Chunk[]}} ResultNode
 * @typedef {{status: Status, durationMs: number, message?: string, detail?: string,
 *            location?: Source, results?: ResultNode[], description?: string,
 *            seed?: string}} Outcome
 * @typedef {{phase: string, chunks: Chunk[], results: ResultNode[], startTime: number,
 *            startedAt: number, buildMs: number, execStartTime: number}} RunFields
 *
 * The run's lifecycle as a single state, so the widget shows exactly one of a spinner, a verdict,
 * an error, or nothing:
 *
 *   idle       no run for this test, and no recorded outcome to show
 *   running    a run is in progress, streaming output; its phase is "starting" until the server
 *              has accepted the run, then "building" and "running" as the server reports
 *   done       a finished run's outcome (live or restored from the session cache)
 *   cancelled  the run was stopped before it produced an outcome
 *   failed     the run could not be carried out at all
 *
 * Every state past idle carries the run's output so far and its timings. The server records the
 * timings per run, so they survive the widget being remounted while the run continues. `startTime`
 * is the start on the server's wall clock, shown as a time of day; `startedAt` is the same instant
 * on the client's clock, which the elapsed counter ticks from, so a server on a remote machine with
 * a different clock still yields the right elapsed time.
 *
 * @typedef {{tag: "idle"}
 *   | ({tag: "running"} & RunFields)
 *   | ({tag: "done", outcome: Outcome} & RunFields)
 *   | ({tag: "cancelled"} & RunFields)
 *   | ({tag: "failed", error: string} & RunFields)} RunUi
 */

/** @type {RunUi} */
const idleState = { tag: "idle" };

/** @returns {RunFields} */
function blankFields() {
    return {
        phase: "",
        chunks: [],
        results: [],
        startTime: 0,
        startedAt: 0,
        buildMs: 0,
        execStartTime: 0,
    };
}

/**
 * A run's result, before anything is known of it beyond where it sits.
 * @returns {ResultNode}
 */
function blankResult(id) {
    return {
        id,
        parent: 0,
        name: "",
        status: "",
        durationMs: 0,
        message: "",
        detail: "",
        location: null,
        output: [],
    };
}

/**
 * The results of a run, updated with the chunks and the reports from named results in one reply.
 *
 * A report gives a result's identifier, parent, and name when it starts, and its verdict when it
 * finishes. A result's output is the chunks whose `result` field names it. All of one result's
 * chunks in a reply are appended at once, so its output array is rebuilt once per reply. The chunk
 * objects are shared with the run's own output, so a result holds only references to them.
 *
 * @param results {ResultNode[]}
 * @returns {ResultNode[]}
 */
function mergeResults(results, reply) {
    const next = results.slice();
    function at(id) {
        while (next.length <= id) next.push(blankResult(next.length));
        return next[id];
    }
    for (const ev of reply.results || []) {
        const shown = at(ev.id);
        next[ev.id] = {
            ...shown,
            parent: ev.parent || 0,
            name: ev.name || shown.name,
            status: ev.status || shown.status,
            durationMs: ev.durationMs || shown.durationMs,
            message: ev.message || shown.message,
            detail: ev.detail || shown.detail,
            location: ev.location || shown.location,
        };
    }
    const arrived = new Map();
    for (const c of reply.chunks || []) {
        const id = c.result || 0;
        if (!arrived.has(id)) arrived.set(id, []);
        arrived.get(id).push(c);
    }
    for (const [id, added] of arrived) {
        const shown = at(id);
        next[id] = { ...shown, output: shown.output.concat(added) };
    }
    return next;
}

/**
 * The results of a finished run, as the outcome records them, each with the output of its own code.
 * A remounted widget shows these, since the run's chunks are gone by then.
 * @returns {ResultNode[]}
 */
function resultsOfOutcome(outcome) {
    const results = (outcome && outcome.results) || [];
    return results.map(function (r) {
        return {
            ...blankResult(r.id || 0),
            parent: r.parent || 0,
            name: r.name || "",
            status: r.status || "",
            durationMs: r.durationMs || 0,
            message: r.message || "",
            detail: r.detail || "",
            location: r.location || null,
            output: r.output || [],
        };
    });
}

/**
 * Every result's output, the results in the order they ran, for a run whose own chunks are gone.
 * @param results {ResultNode[]}
 * @returns {Chunk[]}
 */
function allOutput(results) {
    const all = [];
    for (const result of results) for (const chunk of result.output) all.push(chunk);
    return all;
}

/**
 * Whether each result, or any result below it, failed or raised an error. A named result has a
 * higher identifier than the result that contains it, so one pass from the last result to the first
 * marks every result above a failure.
 * @param results {ResultNode[]}
 * @returns {boolean[]}
 */
function failingPaths(results) {
    const failing = results.map(function (result) {
        return result.status === "failed" || result.status === "error";
    });
    for (let i = results.length - 1; i > 0; i--) {
        if (failing[i]) failing[results[i].parent] = true;
    }
    return failing;
}

/**
 * The named results each result contains, by identifier, in the order they started.
 * @param results {ResultNode[]}
 * @returns {number[][]}
 */
function childrenOf(results) {
    const children = results.map(function () {
        return [];
    });
    for (let i = 1; i < results.length; i++) {
        const parent = results[i].parent;
        if (parent >= 0 && parent < children.length && parent !== i) children[parent].push(i);
    }
    return children;
}

/**
 * The run fields of a state; blank for idle.
 * @param st {RunUi}
 * @returns {RunFields}
 */
function fieldsOf(st) {
    if (st.tag === "idle") return blankFields();
    return {
        phase: st.phase,
        chunks: st.chunks,
        results: st.results,
        startTime: st.startTime,
        startedAt: st.startedAt,
        buildMs: st.buildMs,
        execStartTime: st.execStartTime,
    };
}

/**
 * A finished state showing a recorded outcome, with no live chunks or timings of its own.
 * @param outcome {Outcome}
 * @returns {RunUi}
 */
function doneState(outcome) {
    return { tag: "done", outcome, ...blankFields() };
}

/**
 * Steps the run state by one event:
 *
 *   start    the user started a run; the client's clock stands in for the start time until the
 *            server reports the authoritative one
 *   started  the server accepted the run, so it can be cancelled
 *   server   a reply from `awaitOutput`; it may arrive in any state, since the widget reconnects
 *            to runs it did not start
 *   cancel   the user stopped the run
 *   fail     an RPC call failed, so there is no run to wait for
 *
 * @param st {RunUi}
 * @param ev {any}
 * @returns {RunUi}
 */
function step(st, ev) {
    switch (ev.type) {
        case "start":
            return { tag: "running", ...blankFields(), phase: "starting", startedAt: ev.now };
        case "started":
            return st.tag === "running" && st.phase === "starting"
                ? { ...st, phase: "building" }
                : st;
        case "server": {
            const res = ev.res;
            // A reply about another run than the one shown (started from a second widget instance
            // for the same test, say) begins from blank fields; otherwise the reply extends the run
            // shown. Zero-valued fields in a reply mean "no news"; the server's values otherwise win.
            const shown = fieldsOf(st);
            const prev =
                res.startTime && shown.startTime && res.startTime !== shown.startTime
                    ? blankFields()
                    : shown;
            // The run's start on the client's clock is set once, from the first reply about the
            // run: the time the reply arrived, less how long the server says the run had been
            // going. Later replies leave it unchanged.
            const synced = prev.startTime !== 0;
            const merged = {
                phase: res.phase || prev.phase,
                chunks:
                    res.chunks && res.chunks.length ? prev.chunks.concat(res.chunks) : prev.chunks,
                results:
                    (res.chunks && res.chunks.length) || (res.results && res.results.length)
                        ? mergeResults(prev.results, res)
                        : prev.results,
                startTime: res.startTime || prev.startTime,
                startedAt: !synced && res.elapsedMs ? ev.now - res.elapsedMs : prev.startedAt,
                buildMs: res.buildMs || prev.buildMs,
                execStartTime: res.execStartTime || prev.execStartTime,
            };
            if (!res.done) return { tag: "running", ...merged };
            if (res.outcome) return { tag: "done", outcome: res.outcome, ...merged };
            // Done without an outcome: nothing is running server-side. That ends a watched run
            // (stopped from elsewhere, or its process died); in any other state it is no news.
            return st.tag === "running" ? { tag: "cancelled", ...merged } : st;
        }
        case "cancel":
            return { tag: "cancelled", ...fieldsOf(st) };
        case "fail":
            // Only a run in progress can fail; a failed probe of a settled state is no news.
            return st.tag === "running" ? { tag: "failed", error: ev.error, ...fieldsOf(st) } : st;
        default:
            return st;
    }
}

/**
 * The InfoView reuses one widget instance for whichever test the cursor is on. Keying the inner
 * component on the test and a hash of its source remounts it whenever either changes, so every
 * piece of per-test state starts fresh and an edited test loses its cached or in-progress run.
 */
export default function RunTestWidget(props) {
    const version = props.version || "";
    const declKey = JSON.stringify(props.decl);
    const rs = useRpcSession();

    // This component outlives the edits that remount the inner one, so an edit to the test is
    // visible here as one declaration's version changing. The run of the version left behind ends
    // with it, releasing the build it holds. The version goes with the request, so a run of the
    // test's current source keeps going, as does the run of a test the cursor has left.
    const shown = React.useRef({ declKey, version });
    React.useEffect(
        function () {
            const prev = shown.current;
            shown.current = { declKey, version };
            if (prev.declKey !== declKey || prev.version === version) return;
            rs.call("Errata.Widget.dropStaleRun", {
                decl: props.decl,
                version: prev.version,
            }).catch(function () {});
        },
        [declKey, version],
    );

    return e(TestRun, { ...props, key: declKey + "@" + version, declKey, version });
}

function TestRun(props) {
    const rs = useRpcSession();
    const ec = React.useContext(EditorContext);
    const version = props.version;
    const declKey = props.declKey;

    const [st, dispatch] = React.useReducer(step, undefined, function () {
        const cached = resultCache.get(declKey);
        return cached && cached.version === version ? doneState(cached.outcome) : idleState;
    });
    // Whether the file has no unsaved changes; the test runs the saved version, so Run is gated on it.
    const [clean, setClean] = React.useState(true);
    // Whether the file has changed since the test's run started, as the server last reported it.
    const [edited, setEdited] = React.useState(false);
    // The seed for property tests as typed, or blank to have one drawn.
    const [seed, setSeed] = React.useState("");
    // Whether the run settings (the seed field) are shown, behind the gear button.
    const [settingsOpen, setSettingsOpen] = React.useState(false);
    // The error from the last cancel that failed, shown while the run it was meant to stop goes on.
    const [cancelError, setCancelError] = React.useState(null);
    // Whether the output disclosure is expanded; open by default, collapsible to hide large output.
    const [outputOpen, setOutputOpen] = React.useState(true);
    // Whether a named result starts open, and the ones the reader has since opened or closed, by
    // identifier. A change of the setting clears those, so the new default reaches the whole tree.
    const [expandNamed, setExpandNamed] = React.useState(false);
    const [openResults, setOpenResults] = React.useState({});
    // Whether the widget's own disclosure is expanded, alongside the InfoView's other sections.
    const [panelOpen, setPanelOpen] = React.useState(true);
    // Bumped when the language server restarts, so the widget connects again through its new session.
    const [epoch, setEpoch] = React.useState(0);

    // The RPC session, which the InfoView replaces on every cursor move and after a server restart.
    // Calls go through the latest one, while the connection to the run is made once per mount and
    // once per restart. Each session gets the retry budget in full, so that a run followed across
    // many cursor moves keeps the whole of it for the session it is on.
    const rsRef = React.useRef(rs);
    React.useEffect(function () {
        if (rsRef.current !== rs) awaitFails.current = 0;
        rsRef.current = rs;
    });
    // Bumped on each run start, cancel, and disconnect so a superseded await loop ignores late replies.
    const gen = React.useRef(0);
    // The positions past the chunks and the named-result reports already received, from the
    // server's last reply.
    const sinceRef = React.useRef(0);
    const sinceResultsRef = React.useRef(0);
    // The last phase the widget saw; "" forces the next await to return the run's current phase at once.
    const phaseRef = React.useRef("");
    // Whether the widget is connected, so late clean-check replies are dropped.
    const alive = React.useRef(false);
    // The pending re-check while the buffer is dirty, so a fresh check replaces it.
    const cleanTimer = React.useRef(null);
    // Bumped on each edit and each clean check, so a check begun before an edit reports nothing.
    const cleanGen = React.useRef(0);
    // The start time of the run being followed, so a reply about another one is recognized.
    const shownStart = React.useRef(0);
    // Rejected `awaitOutput` calls since the last reply, and the pending retry of the last of them.
    const awaitFails = React.useRef(0);
    const retryTimer = React.useRef(null);
    // The gear the run settings hang from, and the seed field they hold.
    const gearRef = React.useRef(null);
    const seedRef = React.useRef(null);
    // The file this widget belongs to, from the InfoView's position context. That context is what
    // the widget's RPC session is opened at, so it is here for as long as the widget can call the
    // server at all.
    const uri = React.useContext(EnvPosContext).uri;

    const running = st.tag === "running";
    const starting = st.tag === "running" && st.phase === "starting";

    // Asks the server about the file: whether it is saved, and whether it has changed since the
    // test's run started. The server holds the document as it is being edited and the run as it was
    // started, so it answers both however the widget came to be mounted. It asks again every 1.5 s
    // while the widget is up, so an edit anywhere in the file and a save both show shortly after.
    function checkFile() {
        if (cleanTimer.current) {
            clearTimeout(cleanTimer.current);
            cleanTimer.current = null;
        }
        const myGen = cleanGen.current + 1;
        cleanGen.current = myGen;
        rsRef.current.call("Errata.Widget.fileState", { decl: props.decl }).then(
            function (file) {
                if (!alive.current || cleanGen.current !== myGen) return;
                setClean(file.clean);
                setEdited(file.changedSinceRun);
                cleanTimer.current = setTimeout(checkFile, 1500);
            },
            function () {
                if (!alive.current || cleanGen.current !== myGen) return;
                cleanTimer.current = setTimeout(checkFile, 1500);
            },
        );
    }

    function loop(myGen) {
        rsRef.current
            .call("Errata.Widget.awaitOutput", {
                decl: props.decl,
                since: sinceRef.current,
                sinceResults: sinceResultsRef.current,
                version: version,
                phase: phaseRef.current,
            })
            .then(
                function (res) {
                    if (gen.current !== myGen) return;
                    awaitFails.current = 0;
                    // A reply about another run than the one being followed, started from a second
                    // widget instance for the same test: its output is read from the first chunk.
                    if (
                        res.startTime &&
                        shownStart.current &&
                        res.startTime !== shownStart.current
                    ) {
                        shownStart.current = res.startTime;
                        sinceRef.current = 0;
                        sinceResultsRef.current = 0;
                        phaseRef.current = "";
                        loop(myGen);
                        return;
                    }
                    if (res.startTime) shownStart.current = res.startTime;
                    if (res.phase) phaseRef.current = res.phase;
                    sinceRef.current = res.nextSince || 0;
                    sinceResultsRef.current = res.nextSinceResults || 0;
                    dispatch({ type: "server", res: res, now: Date.now() });
                    if (!res.done) loop(myGen);
                },
                function (err) {
                    if (gen.current !== myGen) return;
                    // The session that rejected the call has been replaced by the time the retry
                    // goes out, so the run is followed on through the new one.
                    if (awaitFails.current < AWAIT_RETRIES) {
                        awaitFails.current += 1;
                        retryTimer.current = setTimeout(function () {
                            if (gen.current === myGen) loop(myGen);
                        }, AWAIT_RETRY_MS * awaitFails.current);
                        return;
                    }
                    dispatch({ type: "fail", error: errorMessage(err) });
                },
            );
    }

    // Connect to any run in progress for this test, replaying its output from the start, and find
    // out whether the buffer is saved. Runs on mount and again after a server restart, through the
    // session the InfoView made for the new server.
    React.useEffect(
        function () {
            const myGen = gen.current + 1;
            gen.current = myGen;
            sinceRef.current = 0;
            sinceResultsRef.current = 0;
            phaseRef.current = "";
            shownStart.current = 0;
            awaitFails.current = 0;
            loop(myGen);
            alive.current = true;
            checkFile();
            return function () {
                gen.current += 1;
                alive.current = false;
                if (cleanTimer.current) clearTimeout(cleanTimer.current);
                cleanTimer.current = null;
                if (retryTimer.current) clearTimeout(retryTimer.current);
                retryTimer.current = null;
            };
        },
        [epoch],
    );

    useEvent(
        ec.events.serverRestarted,
        function () {
            setEpoch(function (n) {
                return n + 1;
            });
        },
        [],
    );

    // The cache mirrors the settled state: a verdict is recorded, and a run that starts, is
    // cancelled, or fails clears it, so a remount shows only the latest result.
    React.useEffect(
        function () {
            if (st.tag === "done") cacheResult(declKey, { version, outcome: st.outcome });
            else if (st.tag !== "idle") resultCache.delete(declKey);
        },
        [st.tag, st.tag === "done" ? st.outcome : null],
    );

    // The seed field takes focus with its value selected when the settings open, so a seed can be
    // typed or replaced straight away.
    React.useEffect(
        function () {
            if (settingsOpen && seedRef.current) seedRef.current.select();
        },
        [settingsOpen],
    );

    // A result the reader has opened or closed stays as they left it. Otherwise the settings
    // decide, except on the way down to a result that did not pass: that path is open, so a failure
    // and the results it happened in are in view as soon as the run reports them.
    // Has the editor open a file at the check that failed, with the check itself selected.
    function reveal(source) {
        const shown = ec.revealLocation({
            uri: source.uri,
            range: {
                start: { line: source.startLine, character: source.startColumn },
                end: { line: source.endLine, character: source.endColumn },
            },
        });
        if (shown && shown.catch) shown.catch(function () {});
    }

    function isResultOpen(id, failing) {
        return id in openResults ? openResults[id] : expandNamed || failing[id];
    }

    function setResultOpen(id, open) {
        setOpenResults(function (opened) {
            return { ...opened, [id]: open };
        });
    }

    function setNamedResultsOpen(open) {
        setExpandNamed(open);
        setOpenResults({});
    }

    function closeSettings(refocus) {
        setSettingsOpen(false);
        if (refocus && gearRef.current) gearRef.current.focus();
    }

    const seedText = seed.trim();
    const seedSet = seedText !== "";
    // A blank seed has one drawn; otherwise it is a natural number, which travels as its digits.
    const seedValid = !seedSet || /^\d+$/.test(seedText);
    const seedHint = "The seed must be a natural number";

    function run() {
        const myGen = gen.current + 1;
        gen.current = myGen;
        sinceRef.current = 0;
        sinceResultsRef.current = 0;
        phaseRef.current = "building";
        shownStart.current = 0;
        awaitFails.current = 0;
        setCancelError(null);
        setEdited(false);
        // A run's results are its own, so they open as the settings and its failures decide rather
        // than as the reader left the run before it.
        setOpenResults({});
        dispatch({ type: "start", now: Date.now() });
        const request = {
            decl: props.decl,
            module: props.module,
            version: version,
        };
        if (seedSet) request.seed = seedText;
        rsRef.current.call("Errata.Widget.startTest", request).then(
            function () {
                if (gen.current !== myGen) return;
                dispatch({ type: "started" });
                loop(myGen);
            },
            function (err) {
                if (gen.current !== myGen) return;
                dispatch({ type: "fail", error: errorMessage(err) });
                // A start refused for unsaved changes means the clean state is stale.
                checkFile();
            },
        );
    }

    // The run is reported as cancelled once the server has ended it, so a cancel that does not
    // arrive leaves a running test reported as running, with the reason beside the button.
    function cancel() {
        setCancelError(null);
        rsRef.current.call("Errata.Widget.cancelTest", { decl: props.decl }).then(
            function () {
                gen.current += 1;
                dispatch({ type: "cancel" });
            },
            function (err) {
                setCancelError(errorMessage(err));
            },
        );
    }

    const name = props.name || "test";

    // What to say about the file beside the button. That the result on show came from the file as
    // it was before a change is a state of the result, so it reads as the verdict does. That the
    // file has to be saved before a run is an instruction, so it reads as the other notes do. A run
    // that has yet to report anything has nothing to go stale.
    let fileHint = null;
    if (!running) {
        const stale = edited && st.tag !== "idle";
        const saveNote = clean
            ? null
            : e(
                  "span",
                  { key: "save", style: { color: dimColor, fontSize: dimSize } },
                  stale ? "— save to run" : "unsaved — save to run",
              );
        fileHint = stale
            ? e(
                  "span",
                  { style: { display: "inline-flex", alignItems: "baseline", gap: "8px" } },
                  e("span", { key: "modified", style: { fontWeight: 600 } }, "File modified"),
                  saveNote,
              )
            : saveNote;
    }

    const header = e(
        "div",
        { style: { display: "flex", alignItems: "center", gap: "8px" } },
        // Cancel waits for the server to accept the run, so a second click of a double-click on
        // Run finds a disabled button.
        running
            ? e(
                  "button",
                  {
                      key: "cancel",
                      onClick: cancel,
                      disabled: starting,
                      title: starting ? "Starting the run" : undefined,
                  },
                  "Cancel",
              )
            : e(
                  "button",
                  {
                      key: "run",
                      onClick: run,
                      disabled: !clean || !seedValid,
                      title: !clean
                          ? "Save the file to run the test"
                          : !seedValid
                            ? seedHint
                            : undefined,
                  },
                  st.tag === "idle" ? "Run" : "Run again",
              ),
        running && cancelError
            ? e(
                  "span",
                  { style: { color: errorColor, fontSize: dimSize } },
                  "could not cancel: " + cancelError,
              )
            : null,
        fileHint,
        // The seed lives behind the gear, so a rejected one is named here as well, where the
        // disabled button is.
        clean && !seedValid && !running
            ? e(
                  "span",
                  { style: { color: errorColor, fontSize: dimSize } },
                  "invalid seed — see run settings",
              )
            : null,
    );

    // The gear that shows the run settings floats at the right of the title, where the goal
    // sections keep theirs. A click here is the control's own, so it leaves the disclosure as it
    // was.
    const runSettings = e(
        "span",
        {
            className: "fr",
            onClick: function (ev) {
                ev.preventDefault();
            },
        },
        e("button", {
            ref: gearRef,
            onClick: function () {
                setSettingsOpen(function (open) {
                    return !open;
                });
            },
            title: settingsOpen
                ? "Hide run settings"
                : seedSet
                  ? "Run settings (seed " + seedText + ")"
                  : "Run settings",
            "aria-label": "Run settings",
            "aria-expanded": settingsOpen,
            "aria-haspopup": "dialog",
            className: "link pointer dim mh2 codicon codicon-settings-gear",
            style: {
                background: "none",
                border: "none",
                padding: 0,
                color: "var(--vscode-textLink-foreground, #0078d4)",
            },
        }),
    );

    const settingRow = {
        display: "flex",
        alignItems: "center",
        gap: "6px",
        whiteSpace: "nowrap",
        fontSize: dimSize,
    };

    // The settings themselves, in a popup below the gear: the seed for property tests, the reason
    // for a rejected one, and how the named results of a run first appear.
    const settingsPopup = settingsOpen
        ? e(
              Popup,
              { anchor: gearRef.current, onClose: closeSettings },
              e(
                  "label",
                  { style: settingRow },
                  "Seed",
                  e("input", {
                      ref: seedRef,
                      type: "text",
                      inputMode: "numeric",
                      value: seed,
                      placeholder: "random",
                      disabled: running,
                      title: "Seed for property tests; blank chooses one randomly",
                      "aria-invalid": !seedValid,
                      onChange: function (ev) {
                          setSeed(ev.target.value);
                      },
                      style: {
                          width: "12ch",
                          fontFamily: monoFont,
                          outline: seedValid
                              ? undefined
                              : "1px solid var(--vscode-inputValidation-errorBorder, #be1100)",
                      },
                  }),
              ),
              seedValid
                  ? null
                  : e(
                        "div",
                        { style: { marginTop: "4px", fontSize: dimSize, color: errorColor } },
                        seedHint,
                    ),
              e(
                  "label",
                  { style: { ...settingRow, marginTop: "4px" } },
                  e("input", {
                      type: "checkbox",
                      checked: expandNamed,
                      title: "Show what each named result reported, rather than its verdict alone",
                      onChange: function (ev) {
                          setNamedResultsOpen(ev.target.checked);
                      },
                      style: { margin: 0 },
                  }),
                  "Expand named results",
              ),
          )
        : null;

    const outcome = st.tag === "done" ? st.outcome : null;
    const timings = st.tag === "idle" ? null : st;
    const execStartTime = timings ? timings.execStartTime : 0;

    // Prefer the live results, whose chunks have the times the runner stamped on them; otherwise
    // use the ones a cached outcome recorded.
    const liveResults = timings ? timings.results : [];
    const results = liveResults.length ? liveResults : resultsOfOutcome(outcome);
    const kids = childrenOf(results);
    const failing = failingPaths(results);
    // What the test's own code reported, which is what the verdict line and the summary under it
    // show. The outcome's message is the innermost failure's, and that result reports it in the
    // tree itself, so taking it here as well would say it twice. A run with no results at all,
    // such as one whose build failed, has only the outcome to report.
    const own = results.length ? results[0] : null;
    const ownMessage = own ? own.message : (outcome && outcome.message) || "";
    const ownDetail = own ? own.detail : (outcome && outcome.detail) || "";
    const ownLocation = own ? own.location : (outcome && outcome.location) || null;
    const rootOutput = results.length ? results[0].output : [];
    // The whole run's output, in the order the test produced it, which the copy button copies.
    const liveChunks = timings ? timings.chunks : [];
    const allChunks = liveChunks.length ? liveChunks : allOutput(results);
    // Keyed so it keeps its state when the message and detail blocks appear ahead of it.
    const outputSection = rootOutput.length
        ? e(OutputSection, {
              key: "output",
              chunks: rootOutput,
              copy: allChunks,
              execStartTime,
              open: outputOpen,
              onOpenChange: setOutputOpen,
          })
        : null;

    // The named results below the test, each with what it reported inside it.
    const resultTree = kids.length
        ? kids[0].map(function (id) {
              return e(NamedResult, {
                  key: id,
                  id,
                  results,
                  kids,
                  execStartTime,
                  reveal,
                  isOpen: function (resultId) {
                      return isResultOpen(resultId, failing);
                  },
                  onOpenChange: setResultOpen,
              });
          })
        : [];

    // The primary status/progress element, then dimmed badges: start time, build and run durations.
    let primary = null;
    if (st.tag === "running") {
        const label =
            st.phase === "starting"
                ? "Starting… "
                : st.phase === "building"
                  ? "Building… "
                  : "Running… ";
        primary = e(
            "span",
            { style: { color: dimColor } },
            label,
            e(Elapsed, { runStart: st.startedAt }),
        );
    } else if (st.tag === "failed") {
        primary = e("span", { style: { color: errorColor } }, "could not run: " + st.error);
    } else if (st.tag === "done") {
        primary = e(
            "span",
            { style: { fontWeight: 600 } },
            e(
                "span",
                {
                    key: "symbol",
                    "aria-hidden": true,
                    style: { color: STATUS_COLORS[st.outcome.status] || "inherit" },
                },
                STATUS_SYMBOLS[st.outcome.status] || "",
            ),
            " " + (STATUS_LABELS[st.outcome.status] || st.outcome.status),
        );
    } else if (st.tag === "cancelled") {
        primary = e("span", { style: { color: dimColor } }, "cancelled");
    }

    // Dimmed badges after the status: text, and for the seed, a click that fills the seed field.
    const badges = [];
    if (timings && timings.startTime)
        badges.push({ text: "Start " + formatClock(timings.startTime) });
    if (timings && timings.buildMs)
        badges.push({ text: "Build " + formatDuration(timings.buildMs) });
    // The seed is present exactly when the test itself ran, so the run's duration and seed appear
    // for a test that ran and stay hidden for a build or runner failure.
    if (outcome && typeof outcome.seed === "string") {
        const seedUsed = outcome.seed;
        badges.push({ text: "Run " + formatDuration(outcome.durationMs) });
        badges.push({
            text: "Seed " + seedUsed,
            title: "Use this seed for the next run",
            onClick: function () {
                setSeed(seedUsed);
                setSettingsOpen(true);
            },
        });
    }

    const infoRow =
        primary || badges.length
            ? e(
                  "div",
                  {
                      style: {
                          display: "flex",
                          alignItems: "baseline",
                          gap: "8px",
                          flexWrap: "wrap",
                      },
                  },
                  primary,
                  // Each badge is a dot separator and a label. A clickable label is a button,
                  // reachable by keyboard, styled to read like the plain ones.
                  ...badges.map(function (b, i) {
                      return e(
                          "span",
                          { key: i, style: { color: dimColor, fontSize: dimSize } },
                          "· ",
                          b.onClick
                              ? e(
                                    "button",
                                    {
                                        title: b.title,
                                        onClick: b.onClick,
                                        style: {
                                            font: "inherit",
                                            color: "inherit",
                                            background: "none",
                                            border: "none",
                                            padding: 0,
                                            cursor: "pointer",
                                            textDecoration: "underline dotted",
                                        },
                                    },
                                    b.text,
                                )
                              : b.text,
                      );
                  }),
                  // The row is a flex, so the control sits at the end of it rather than floating.
                  ownLocation
                      ? e(
                            "span",
                            { key: "where", style: { marginLeft: "auto" } },
                            sourceButton(ownLocation, reveal),
                        )
                      : null,
              )
            : null;

    const extras = [];
    if (outcome && ownMessage) extras.push(e("div", { key: "msg" }, block(ownMessage)));
    if (outcome && ownDetail) extras.push(e("div", { key: "detail" }, block(ownDetail)));

    // The test's docstring, rendered from the Markdown Lean produced for it, alongside its result.
    const descriptionSection =
        outcome && outcome.description
            ? e(
                  "div",
                  {
                      key: "description",
                      style: { marginTop: "4px" },
                  },
                  e(Markdown, { contents: outcome.description }),
              )
            : null;

    const body =
        infoRow || descriptionSection || extras.length || outputSection || resultTree.length
            ? e(
                  "div",
                  { style: { marginTop: "4px" } },
                  infoRow,
                  descriptionSection,
                  ...extras,
                  outputSection,
                  resultTree.length
                      ? e("div", { key: "results" }, e("style", null, treeStyle), resultTree)
                      : null,
              )
            : null;

    // A disclosure in the InfoView's own style, so the test sits among the goal and message
    // sections. Its content is dropped while collapsed, as those sections do, so a long-running
    // test's output costs nothing to keep out of sight.
    //
    // The pointer arriving means Run may be next, so the file's state is checked at once rather
    // than at the next poll.
    return e(
        "details",
        {
            open: panelOpen,
            onToggle: /** @param ev {React.ToggleEvent<HTMLDetailsElement>} */ function (ev) {
                setPanelOpen(ev.currentTarget.open);
            },
            onMouseEnter: checkFile,
        },
        e(
            "summary",
            { className: "mv2 pointer non-selectable" },
            "Errata test: ",
            e("span", { style: { fontFamily: monoFont, fontSize: "0.95em" } }, name),
            runSettings,
        ),
        settingsPopup,
        panelOpen ? e("div", { className: "ml1" }, header, body) : null,
    );
}
