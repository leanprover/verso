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

// The last settled run of each test, keyed by its declaration and tagged with the source version
// that produced it. Leaving and returning to a test's `@[test]` marker shows its previous result
// again, just as it was shown when the run finished. The most recent RESULT_CACHE_LIMIT of them are
// held, each with the whole of its run's captured output.
/**
 * @typedef {{version: string, outcome: Outcome, fields: RunFields, since: number,
 *   sinceResults: number}} CachedRun a finished run: its outcome, the chunks and results the widget
 *   received, and the positions past them on the server
 * @type {Map<string, CachedRun>}
 */
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
// beside it keeps the editor's text colour. A failure within an `expectFail` is a failure that the
// test wanted, so it keeps the failure's glyph in the muted colour of a skipped test.
const STATUS_COLORS = {
    passed: "var(--vscode-testing-iconPassed, #2e7d32)",
    failed: "var(--vscode-testing-iconFailed, #c62828)",
    error: "var(--vscode-testing-iconErrored, #e65100)",
    expectedFailure: "var(--vscode-testing-iconSkipped, #848484)",
};

const STATUS_SYMBOLS = {
    passed: "✓",
    failed: "✗",
    error: "⚠",
    expectedFailure: "✗",
};

const STATUS_LABELS = {
    passed: "Passed",
    failed: "FAILED",
    error: "ERROR",
    expectedFailure: "Expected failure",
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

// How many rejected calls in a row are retried quietly, the delay that grows with each attempt, and
// the longest delay between attempts. The InfoView replaces the RPC session as the cursor moves,
// which rejects the call in flight, so a rejection is part of the ordinary course of a run.
const AWAIT_RETRIES = 5;
const AWAIT_RETRY_MS = 200;
const AWAIT_RETRY_MAX_MS = 2000;

// The JSON-RPC error code of a call that the server refuses for its parameters.
const INVALID_PARAMS = -32602;

const monoFont = "var(--vscode-editor-font-family, monospace)";

// The editor theme's colour for secondary text: the badges, hints, and the output summary. The
// theme keeps it legible against the InfoView's background.
const dimColor = "var(--vscode-descriptionForeground, #717171)";

// The editor theme's colour for errors: a run that could not start, and a rejected seed.
const errorColor = "var(--vscode-errorForeground, #c62828)";

// The editor theme's colour for warnings: an option that the test never read.
const warningColor = "var(--vscode-editorWarning-foreground, #bf8803)";

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

// The popup opens below its anchor when this much room is there, and otherwise on the side with
// more room. It keeps this far from the edge of the window, and scrolls when it would grow past it.
const POPUP_ROOM = 160;
const POPUP_MARGIN = 8;

// A fixed position against an element, aligned to its right edge and below it, going above it
// where the view has more room there, with a height that stays within the window.
function placeUnder(anchor) {
    if (!anchor) return { display: "none" };
    const rect = anchor.getBoundingClientRect();
    const style = {
        position: "fixed",
        right: Math.max(8, window.innerWidth - rect.right),
        zIndex: 100,
        overflowY: "auto",
    };
    const below = window.innerHeight - rect.bottom - 6 - POPUP_MARGIN;
    const above = rect.top - 6 - POPUP_MARGIN;
    if (below >= POPUP_ROOM || below >= above) {
        style.top = rect.bottom + 6;
        style.maxHeight = below;
    } else {
        style.bottom = window.innerHeight - rect.top + 6;
        style.maxHeight = above;
    }
    return style;
}

// The style of a button that is a codicon alone, dimmed and without the pointer while it is
// disabled.
function iconButtonStyle(disabled) {
    return {
        background: "none",
        border: "none",
        padding: 0,
        color: disabled
            ? "var(--vscode-disabledForeground, #888)"
            : "var(--vscode-textLink-foreground, #0078d4)",
        cursor: disabled ? "default" : undefined,
    };
}

// The outline of a settings field whose text holds back a run.
const invalidOutline = "1px solid var(--vscode-inputValidation-errorBorder, #be1100)";

// Whether an option row has neither a name nor a value. A blank row is left out of a run, and is
// removed when a run starts.
function optionIsBlank(opt) {
    return opt.name.trim() === "" && opt.value === "";
}

// The problem with an option row that holds back a run, or null.
function optionProblem(opt) {
    if (optionIsBlank(opt)) return null;
    const name = opt.name.trim();
    if (name === "") return "Each option needs a name";
    if (name.startsWith("-")) return "Write each option's name without its leading dashes";
    return null;
}

// A word as a POSIX shell reads it: as it is when the shell passes on all of its characters
// unchanged, and in double quotes otherwise.
function shellWord(text) {
    if (/^[A-Za-z0-9_@%+=:,./-]+$/.test(text)) return text;
    return '"' + text.replace(/["\\$`]/g, "\\$&") + '"';
}

// Options as they are written on the test driver's command line.
function optionsCommandLine(opts) {
    return opts
        .map(function (opt) {
            return (
                "--" + shellWord(opt.name) + (opt.value === "" ? "" : "=" + shellWord(opt.value))
            );
        })
        .join(" ");
}

// The value of `focusOptionKey` that gives the focus to the add button.
const ADD_OPTION = "add";

// A popup anchored to an element, in the style of the InfoView's own menus. It is portalled to the
// document body, which puts it outside the disclosure summary that holds its anchor, so the
// controls inside it keep their own keyboard and pointer behaviour. It closes on Escape, on a
// click outside it, and when the view moves under it. `onClose` is told whether to return focus to
// the anchor.
function Popup(props) {
    const anchor = props.anchor;
    const ref = React.useRef(null);
    // Held in a ref, so the listeners are installed once, when the popup opens.
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
const ChunkSpan = React.memo(
    /**
     * @param props {{chunk: Chunk, index: number, execStartTime: number, hovered: boolean,
     *                onHover: (index: number) => void}}
     */
    function ChunkSpan(props) {
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
    },
);

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

// Copying output to the clipboard, for a control that confirms each copy for a moment: `copied` is
// true for a moment after each copy, and `copy` copies the text of the chunks it is given.
function useCopy() {
    const ec = React.useContext(EditorContext);
    const [copied, setCopied] = React.useState(false);
    // The timer that ends the confirmation, so another copy restarts it in full.
    const copiedTimer = React.useRef(null);

    React.useEffect(function () {
        return function () {
            if (copiedTimer.current) clearTimeout(copiedTimer.current);
        };
    }, []);

    function confirmCopy() {
        setCopied(true);
        if (copiedTimer.current) clearTimeout(copiedTimer.current);
        copiedTimer.current = setTimeout(function () {
            copiedTimer.current = null;
            setCopied(false);
        }, 1500);
    }

    /** @param chunks {Chunk[]} */
    function copy(chunks) {
        const text = chunks
            .map(function (c) {
                return c.text;
            })
            .join("");
        // The editor puts the text on the clipboard, and a refused copy leaves the label as it is.
        ec.api.copyToClipboard(text).then(confirmCopy, function () {});
    }

    return { copied, copy };
}

// The copy icon (two overlapping sheets), or a check mark once the output has been copied.
function copyIcon(copied) {
    return e(
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
}

/**
 * A box of output with a copy button floating over its corner, which copies the output in the box.
 * The button is revealed while the pointer is over the box or the button has keyboard focus.
 * @param props {{chunks: Chunk[], children?: React.ReactNode}}
 */
function CopyableOutput(props) {
    const { copied, copy } = useCopy();
    const [over, setOver] = React.useState(false);
    const [focused, setFocused] = React.useState(false);
    const copyButton = e(
        "button",
        {
            onClick: function () {
                copy(props.chunks);
            },
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
        copyIcon(copied),
    );
    return e(
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
        props.children,
    );
}

/**
 * The control in the title that copies the whole run's output, in the order the test produced it.
 * @param props {{chunks: Chunk[]}}
 */
function CopyAllButton(props) {
    const { copied, copy } = useCopy();
    return e("button", {
        onClick: function () {
            copy(props.chunks);
        },
        title: copied ? "Copied" : "Copy all output",
        "aria-label": "Copy all output",
        className: "link pointer dim mh2 codicon " + (copied ? "codicon-check" : "codicon-copy"),
        style: {
            background: "none",
            border: "none",
            padding: 0,
            color: "var(--vscode-textLink-foreground, #0078d4)",
        },
    });
}

// The collapsible output disclosure: a summary naming the hovered chunk's stream and time offset,
// and the interleaved chunks in a box of their own. Whether it is open belongs to the caller, so a
// collapse outlasts the output being replaced.
const OutputSection = React.memo(
    /**
     * @param props {{chunks: Chunk[], length: number, execStartTime: number, open: boolean,
     *                onOpenChange: (open: boolean) => void}}
     */
    function OutputSection(props) {
        const chunks = props.chunks;
        const execStartTime = props.execStartTime;
        // The position of the output chunk under the cursor, highlighted with its timestamp shown, or
        // -1. A position keeps the highlight and the summary in step at any length of output.
        const [hovered, setHovered] = React.useState(-1);
        // The spans of the chunks, from one render to the next.
        const spanCache = React.useRef({ spans: [], last: null, execStartTime: 0 });
        // Whether a chunk of the output on show is under the pointer.
        const showing = hovered >= 0 && hovered < chunks.length;

        return e(
            "details",
            {
                open: props.open,
                onToggle: /** @param ev {React.SyntheticEvent<HTMLDetailsElement>} */ function (
                    ev,
                ) {
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
                CopyableOutput,
                { chunks },
                outputBlock(spanCache, chunks, execStartTime, hovered, setHovered),
            ),
        );
    },
);

// The control that goes to the check a failure came from, as the InfoView's own sections offer a
// place: an icon at the right of the row that names the thing, with where it leads in its tooltip.
// An assertion records its own source position, which is where the control goes.
function sourceButton(source, reveal) {
    if (!source) return null;
    const file = decodeURIComponent((source.uri || "").split("/").pop() || "");
    // Lines and columns counted from one, as the editor's status bar counts them.
    const where = file + ":" + (source.startLine + 1) + ":" + (source.startColumn + 1);
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
// that reported something opens to show it, in the order a reader wants it: its failure message and
// detail, what its own code wrote, then the named results inside it. A result that reported nothing beyond
// its verdict is a row of its own, with no triangle to open.
function NamedResult(props) {
    const result = props.results[props.id];
    // This result's own spans, and the chunk of them under the cursor.
    const spanCache = React.useRef({ spans: [], last: null, execStartTime: 0 });
    const [hovered, setHovered] = React.useState(-1);
    const inside = props.kids[props.id] || [];
    const reported = !!(result.message || result.detail || result.output.length || inside.length);
    const open = reported && props.isOpen(props.id);
    // A result reads as the InfoView's own text, so its rows take the size around them and the tree
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
            onToggle: /** @param ev {React.SyntheticEvent<HTMLDetailsElement>} */ function (ev) {
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
                      ? e(
                            CopyableOutput,
                            { key: "output", chunks: result.output },
                            outputBlock(
                                spanCache,
                                result.output,
                                props.execStartTime,
                                hovered,
                                setHovered,
                            ),
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
 * @typedef {"passed" | "failed" | "error" | "expectedFailure"} Status the verdict of a result, as
 *   Lean reports it
 * @typedef {Status | ""} ShownStatus a verdict, or blank while a result is still running
 * @typedef {{uri: string, startLine: number, startColumn: number, endLine: number,
 *            endColumn: number}} Source the span of a failed check
 * @typedef {{stream: string, text: string, time?: number, result?: number}} Chunk
 * @typedef {{id: number, parent: number, name: string, status: ShownStatus, durationMs: number,
 *            message: string, detail: string, location: Source | null,
 *            output: Chunk[]}} ResultNode
 * @typedef {{status: Status, durationMs: number, message?: string, detail?: string,
 *            location?: Source, results?: ResultNode[], description?: string,
 *            seed?: string, options?: {name: string, value: string}[],
 *            unreadOptions?: string[]}} Outcome
 * @typedef {{phase: string, chunks: Chunk[], results: ResultNode[], startTime: number,
 *            startedAt: number, buildMs: number, execStartTime: number,
 *            runId: string}} RunFields
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
        runId: "",
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
 * The chunks of a run, with those of one reply at their positions in the run. A reply holds the run's
 * chunks from a position on, so a chunk that a replayed reply holds again lands where it already is.
 * The array grows in place, since a run's output only grows, so a reply costs as much as the chunks
 * it holds.
 *
 * @param chunks {Chunk[]}
 * @returns {Chunk[]}
 */
function placeChunks(chunks, reply) {
    const added = reply.chunks || [];
    const start = Math.max(0, (reply.nextSince || 0) - added.length);
    for (let i = 0; i < added.length && start + i <= chunks.length; i++) {
        chunks[start + i] = added[i];
    }
    return chunks;
}

/**
 * The output of each result, by identifier: the chunks whose `result` field names it, in order. The
 * groups live in `cache` from one render to the next and take in only the chunks that arrived since,
 * so a run's output is grouped once as it grows. Chunks that replaced the ones grouped, such as those
 * of another run, start the groups over.
 *
 * @param chunks {Chunk[]}
 * @returns {Map<number, Chunk[]>}
 */
function outputsByResult(cache, chunks) {
    const c = cache.current;
    if (c.chunks !== chunks || c.count > chunks.length) {
        c.chunks = chunks;
        c.count = 0;
        c.byResult = new Map();
    }
    for (; c.count < chunks.length; c.count++) {
        const chunk = chunks[c.count];
        const id = chunk.result || 0;
        let group = c.byResult.get(id);
        if (!group) {
            group = [];
            c.byResult.set(id, group);
        }
        group.push(chunk);
    }
    return c.byResult;
}

/**
 * The results of a run, updated with the reports from named results in one reply. A report gives a
 * result's identifier, parent, and name when it starts, and its verdict when it finishes. A replayed
 * report updates a result with what it already holds.
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
    // A chunk can name a result that has yet to be reported, such as the test's own.
    for (const c of reply.chunks || []) at(c.result || 0);
    return next;
}

/**
 * The results of a finished run, as the outcome records them. The runner streams each result's
 * output as it is written, so these hold none. A widget that has none of the run's live results
 * shows these.
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
        // A named result has a higher identifier than the result that holds it, so a parent at or
        // above a result's own identifier belongs to no tree and its result is left out.
        if (parent >= 0 && parent < i) children[parent].push(i);
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
        runId: st.runId,
    };
}

/**
 * Whether a reply is about another run than the one shown. Replies name their run by the identifier
 * that the widget gave it; a run started without one is told apart by its start time.
 * @param shown {{runId: string, startTime: number}}
 */
function isOtherRun(shown, reply) {
    if (reply.runId && shown.runId) return reply.runId !== shown.runId;
    return !!(reply.startTime && shown.startTime && reply.startTime !== shown.startTime);
}

/**
 * A finished state showing a cached run, with the chunks, results, and timings it had.
 * @param cached {CachedRun}
 * @returns {RunUi}
 */
function doneState(cached) {
    return { tag: "done", outcome: cached.outcome, ...cached.fields };
}

/**
 * Steps the run state by one event:
 *
 *   start    the user started a run; the client's clock stands in for the start time until the
 *            server reports the authoritative one
 *   started  the server accepted the run, so it can be cancelled
 *   server   a reply from `awaitOutput`; it may arrive in any state, since the widget reconnects
 *            to runs that another widget started
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
            return {
                tag: "running",
                ...blankFields(),
                phase: "starting",
                startedAt: ev.now,
                runId: ev.runId,
            };
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
            const prev = isOtherRun(shown, res) ? blankFields() : shown;
            // The run's start on the client's clock is set once, from the first reply about the
            // run: the time the reply arrived, less how long the server says the run had been
            // going. Later replies leave it unchanged.
            const synced = prev.startTime !== 0;
            const merged = {
                phase: res.phase || prev.phase,
                chunks: placeChunks(prev.chunks, res),
                results:
                    (res.chunks && res.chunks.length) || (res.results && res.results.length)
                        ? mergeResults(prev.results, res)
                        : prev.results,
                startTime: res.startTime || prev.startTime,
                startedAt: !synced && res.elapsedMs ? ev.now - res.elapsedMs : prev.startedAt,
                buildMs: res.buildMs || prev.buildMs,
                execStartTime: res.execStartTime || prev.execStartTime,
                runId: res.runId || prev.runId,
            };
            if (!res.done) return { tag: "running", ...merged };
            // A cancel and a refused start are states of the widget's own, which a reply about the
            // run leaves as they are.
            if (st.tag === "cancelled" || st.tag === "failed") return st;
            if (res.outcome) return { tag: "done", outcome: res.outcome, ...merged };
            // Done without an outcome: nothing is running server-side. That ends a watched run
            // (stopped from elsewhere, or its process died); in any other state it is no news.
            return st.tag === "running" ? { tag: "cancelled", ...merged } : st;
        }
        case "cancel":
            // A run that finished while the cancel was on its way keeps its outcome.
            return st.tag === "running" ? { tag: "cancelled", ...fieldsOf(st) } : st;
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
 * piece of per-test state starts fresh and an edited test loses its cached or in-progress run. The
 * server ends the run of an edited test as it elaborates the edit.
 */
export default function RunTestWidget(props) {
    const version = props.version || "";
    // The file and the declaration together name the test, since two files can each hold a test of
    // the same name and source. The InfoView opens the widget's RPC session at this file.
    const uri = React.useContext(EnvPosContext).uri;
    const declKey = uri + " " + JSON.stringify(props.decl);
    return e(TestRun, { ...props, key: declKey + "@" + version, declKey, version });
}

function TestRun(props) {
    const rs = useRpcSession();
    const ec = React.useContext(EditorContext);
    const version = props.version;
    const declKey = props.declKey;

    const [st, dispatch] = React.useReducer(step, undefined, function () {
        const cached = resultCache.get(declKey);
        return cached && cached.version === version ? doneState(cached) : idleState;
    });
    // Whether the file has no unsaved changes; the test runs the saved version, so Run is gated on
    // it. It is null until the server has said, which holds Run back until the answer is in.
    const [clean, setClean] = React.useState(null);
    // Whether the file has changed since the test's run started, as the server last reported it.
    const [edited, setEdited] = React.useState(false);
    // The seed for property tests as typed, or blank to generate a random seed.
    const [seed, setSeed] = React.useState("");
    // The test options as typed, one row for each, in order. Each row has a key of
    // its own, so removing a row leaves the text of the rows after it where it was.
    const [options, setOptions] = React.useState([]);
    const nextOptionKey = React.useRef(0);
    // What takes the focus when the rows are next shown: the name field of the row with this key, or
    // the add button for ADD_OPTION. A row that is added or removed sets it.
    const focusOptionKey = React.useRef(null);
    // Whether the run settings are shown, behind the gear button.
    const [settingsOpen, setSettingsOpen] = React.useState(false);
    // The error from the last cancel that failed, shown while the run it was meant to stop goes on.
    const [cancelError, setCancelError] = React.useState(null);
    // The error from the latest of a run of rejected reports, shown while the widget keeps asking.
    const [awaitError, setAwaitError] = React.useState(null);
    // Whether the output disclosure is expanded; open by default, collapsible to hide large output.
    const [outputOpen, setOutputOpen] = React.useState(true);
    // Whether a named result starts open, and the ones the reader has since opened or closed, by
    // identifier. A change of the setting clears those, so the new default reaches the whole tree.
    const [expandNamed, setExpandNamed] = React.useState(false);
    const [openResults, setOpenResults] = React.useState({});
    // Whether the widget's own disclosure is expanded, alongside the InfoView's other sections.
    const [open, setOpen] = React.useState(true);
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
    // The identifier and start time of the run being followed, so a reply about another is recognized.
    const shownRun = React.useRef({ runId: "", startTime: 0 });
    // Rejected `awaitOutput` calls since the last reply, and the pending retry of the last of them.
    const awaitFails = React.useRef(0);
    const retryTimer = React.useRef(null);
    // The gear the run settings hang from, and the seed field they hold.
    const gearRef = React.useRef(null);
    const seedRef = React.useRef(null);
    // The output of each result, grouped from the run's chunks as they arrive.
    const outputCache = React.useRef({ chunks: null, count: 0, byResult: new Map() });

    const running = st.tag === "running";
    // Whether a run is in progress, for the replies that arrive after the render that started them.
    const runningRef = React.useRef(running);
    React.useEffect(function () {
        runningRef.current = running;
    });
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
        // A reply to a check sent before a run started is about the run before it.
        const runGen = gen.current;
        rsRef.current.call("Errata.Widget.fileState", { decl: props.decl }).then(
            function (file) {
                if (!alive.current || cleanGen.current !== myGen) return;
                setClean(file.clean);
                if (gen.current === runGen) setEdited(file.changedSinceRun);
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
                    setAwaitError(null);
                    // A reply about another run than the one being followed, started from a second
                    // widget instance for the same test: its output is read from the first chunk.
                    if (isOtherRun(shownRun.current, res)) {
                        shownRun.current = { runId: res.runId, startTime: res.startTime };
                        sinceRef.current = 0;
                        sinceResultsRef.current = 0;
                        phaseRef.current = "";
                        loop(myGen);
                        return;
                    }
                    shownRun.current = {
                        runId: res.runId || shownRun.current.runId,
                        startTime: res.startTime || shownRun.current.startTime,
                    };
                    if (res.phase) phaseRef.current = res.phase;
                    sinceRef.current = res.nextSince || 0;
                    sinceResultsRef.current = res.nextSinceResults || 0;
                    dispatch({ type: "server", res: res, now: Date.now() });
                    if (!res.done) loop(myGen);
                },
                function (err) {
                    if (gen.current !== myGen) return;
                    // The session that rejected the call has been replaced by the time the retry
                    // goes out, so the run is followed on through the new one. A run in progress
                    // is followed for as long as the widget is up: past the first few retries, the
                    // widget names the error beside the Cancel button and keeps trying at a slower
                    // pace. A widget with no run in progress stops asking after the first few.
                    awaitFails.current += 1;
                    if (awaitFails.current > AWAIT_RETRIES) {
                        if (!runningRef.current) return;
                        setAwaitError(errorMessage(err));
                    }
                    retryTimer.current = setTimeout(
                        function () {
                            if (gen.current === myGen) loop(myGen);
                        },
                        Math.min(AWAIT_RETRY_MS * awaitFails.current, AWAIT_RETRY_MAX_MS),
                    );
                },
            );
    }

    // Connect to any run in progress for this test, and find out whether the buffer is saved. Runs on
    // mount and again after a server restart, through the session the InfoView made for the new
    // server. A run restored from the cache is followed from where the cache left it, so the server
    // sends only what came after; any other run's output is replayed from the start.
    React.useEffect(
        function () {
            const myGen = gen.current + 1;
            gen.current = myGen;
            const cached = resultCache.get(declKey);
            const resumed =
                st.tag === "done" && cached && cached.outcome === st.outcome ? cached : null;
            sinceRef.current = resumed ? resumed.since : 0;
            sinceResultsRef.current = resumed ? resumed.sinceResults : 0;
            phaseRef.current = "";
            shownRun.current = resumed
                ? { runId: resumed.fields.runId, startTime: resumed.fields.startTime }
                : { runId: "", startTime: 0 };
            awaitFails.current = 0;
            setAwaitError(null);
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
            if (st.tag === "done") {
                cacheResult(declKey, {
                    version,
                    outcome: st.outcome,
                    fields: fieldsOf(st),
                    since: sinceRef.current,
                    sinceResults: sinceResultsRef.current,
                });
            } else if (st.tag !== "idle") resultCache.delete(declKey);
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

    // A result the reader has opened or closed stays as they left it. Otherwise the settings
    // decide, except on the way down to a result that failed or erred: that path is open, so a failure
    // and the results it happened in are in view as soon as the run reports them.
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
    // A blank seed means that a random seed is generated; otherwise it is a natural number, which
    // travels as its digits.
    const seedValid = !seedSet || /^\d+$/.test(seedText);
    const seedHint = "The seed must be a natural number";
    const optionsSent = options
        .filter(function (opt) {
            return !optionIsBlank(opt);
        })
        .map(function (opt) {
            return { name: opt.name.trim(), value: opt.value };
        });
    const optionsSet = optionsSent.length > 0;
    // The names of the options that the shown run gave the test and the test never read.
    const unreadOptions = (st.tag === "done" && st.outcome.unreadOptions) || [];
    // The first problem among the rows, which holds back the run until it is fixed.
    const optionsHint = options.map(optionProblem).find(Boolean) || null;
    const optionsValid = optionsHint === null;
    // What the settings hold, named in the gear's tooltip so a run's settings show while the popup
    // is closed.
    const settingsSummary = (seedSet ? ["seed " + seedText] : [])
        .concat(optionsSet ? ["options " + optionsCommandLine(optionsSent)] : [])
        .join(", ");

    function addOption() {
        const key = nextOptionKey.current++;
        focusOptionKey.current = key;
        setOptions(function (opts) {
            return opts.concat([{ key, name: "", value: "" }]);
        });
    }

    // Fills the rows with the options of an earlier run, so the next run repeats them.
    function repeatOptions(opts) {
        setOptions(
            opts.map(function (opt) {
                return { key: nextOptionKey.current++, name: opt.name, value: opt.value };
            }),
        );
    }

    function editOption(key, field, text) {
        setOptions(function (opts) {
            return opts.map(function (opt) {
                return opt.key === key ? { ...opt, [field]: text } : opt;
            });
        });
    }

    // Removes a row. The focus moves to the row that takes its place, or to the one before it when
    // it was the last, or to the add button when no rows are left.
    function removeOption(key) {
        const i = options.findIndex(function (opt) {
            return opt.key === key;
        });
        const next = options[i + 1] || options[i - 1];
        focusOptionKey.current = next ? next.key : ADD_OPTION;
        setOptions(function (opts) {
            return opts.filter(function (opt) {
                return opt.key !== key;
            });
        });
    }

    function run() {
        const myGen = gen.current + 1;
        gen.current = myGen;
        sinceRef.current = 0;
        sinceResultsRef.current = 0;
        phaseRef.current = "building";
        // The server's replies about the run carry this identifier, so the run this click started is
        // told apart from any other run of the test.
        const runId = Math.random().toString(36).slice(2) + Date.now().toString(36);
        shownRun.current = { runId, startTime: 0 };
        awaitFails.current = 0;
        setCancelError(null);
        setAwaitError(null);
        setEdited(false);
        // Each run's results open as the settings and its failures decide.
        setOpenResults({});
        setOptions(function (opts) {
            return opts.filter(function (opt) {
                return !optionIsBlank(opt);
            });
        });
        dispatch({ type: "start", now: Date.now(), runId });
        const request = {
            decl: props.decl,
            module: props.module,
            version: version,
            runId: runId,
        };
        if (seedSet) request.seed = seedText;
        if (optionsSet) request.options = optionsSent;
        rsRef.current.call("Errata.Widget.startTest", request).then(
            function () {
                if (gen.current !== myGen) return;
                dispatch({ type: "started" });
                loop(myGen);
            },
            function (err) {
                if (gen.current !== myGen) return;
                function refused() {
                    dispatch({ type: "fail", error: errorMessage(err) });
                    // A start refused for unsaved changes means the clean state is stale.
                    checkFile();
                }
                // The server refuses a start with invalid parameters, such as unsaved changes or a
                // malformed seed. Any other rejection can come from a session that the InfoView
                // replaced after the server had started the run, so the server is asked once
                // whether it holds the run with this click's identifier, and the widget follows
                // that run.
                if (err && err.code === INVALID_PARAMS) {
                    refused();
                    return;
                }
                rsRef.current
                    .call("Errata.Widget.awaitOutput", {
                        decl: props.decl,
                        since: 0,
                        sinceResults: 0,
                        version: version,
                        phase: "",
                    })
                    .then(
                        function (res) {
                            return res.runId === runId;
                        },
                        function () {
                            return false;
                        },
                    )
                    .then(function (started) {
                        if (gen.current !== myGen) return;
                        if (!started) {
                            refused();
                            return;
                        }
                        dispatch({ type: "started" });
                        loop(myGen);
                    });
            },
        );
    }

    // The run is reported as cancelled once the server has ended it. Until then the run is reported
    // as running, and a cancel that keeps failing shows its reason beside the button.
    function cancel() {
        setCancelError(null);
        // A reply that arrives after a new run has started is about the run before it. A rejected
        // call is tried again through the latest session, as a rejected report is.
        const myGen = gen.current;
        // The run as it stands at the click, so a retry names the run the reader asked to stop even
        // when a reply has since pointed the widget at another run of the test.
        const runId = shownRun.current.runId;
        function attempt(failures) {
            const request = { decl: props.decl, runId: runId };
            rsRef.current.call("Errata.Widget.cancelTest", request).then(
                function (res) {
                    if (gen.current !== myGen) return;
                    // A run that had finished by the time the cancel arrived keeps its outcome, so
                    // the widget goes on reading the run and shows what it reported.
                    if (res && res.cancelled === false) return;
                    gen.current += 1;
                    setAwaitError(null);
                    dispatch({ type: "cancel" });
                },
                function (err) {
                    if (gen.current !== myGen) return;
                    if (failures < AWAIT_RETRIES) {
                        setTimeout(
                            function () {
                                if (alive.current && gen.current === myGen) attempt(failures + 1);
                            },
                            AWAIT_RETRY_MS * (failures + 1),
                        );
                        return;
                    }
                    setCancelError(errorMessage(err));
                },
            );
        }
        attempt(0);
    }

    const name = props.name || "test";

    // What to say about the file beside the button. That the result on show came from the file as
    // it was before a change is a state of the result, so it reads as the verdict does. That the
    // file has to be saved before a run is an instruction, so it reads as the other notes do. A run
    // that has yet to report anything has nothing to go stale.
    let fileHint = null;
    if (!running) {
        const stale = edited && st.tag !== "idle";
        const saveNote =
            clean !== false
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
                      disabled: !clean || !seedValid || !optionsValid,
                      title:
                          clean === null
                              ? "Checking whether the file is saved"
                              : !clean
                                ? "Save the file to run the test"
                                : !seedValid
                                  ? seedHint
                                  : !optionsValid
                                    ? optionsHint
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
        running && awaitError
            ? e(
                  "span",
                  { style: { color: errorColor, fontSize: dimSize } },
                  "reconnecting: " + awaitError,
              )
            : null,
        fileHint,
        // The seed and the options live behind the gear, so a rejected one is named here as well,
        // where the disabled button is.
        clean && (!seedValid || !optionsValid) && !running
            ? e(
                  "span",
                  { style: { color: errorColor, fontSize: dimSize } },
                  (!seedValid ? "invalid seed" : "invalid option") + " — see run settings",
              )
            : null,
    );

    // The gear that shows the run settings, one of the controls at the right of the title.
    const gearButton = e("button", {
        key: "settings",
        ref: gearRef,
        onClick: function () {
            setSettingsOpen(function (open) {
                return !open;
            });
        },
        title: settingsOpen
            ? "Hide run settings"
            : settingsSummary
              ? "Run settings (" + settingsSummary + ")"
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
    });

    const settingRow = {
        display: "flex",
        alignItems: "center",
        gap: "6px",
        whiteSpace: "nowrap",
        fontSize: dimSize,
    };

    const hintStyle = { marginTop: "4px", fontSize: dimSize, color: errorColor };
    // The buttons that add and remove options are disabled during a run, and look like links only
    // while they can be clicked.
    const iconButtonClass = running ? "codicon" : "link pointer dim codicon";
    // Each option is laid out as it is written on the command line, `--name=value`, followed by its
    // remove button and, for an option that the last run never read, a warning. Every row has the
    // same columns, so the rows and the add button below them line up.
    const optionRow = {
        display: "grid",
        gridTemplateColumns: "2ch 12ch 1ch 14ch 22px 22px",
        alignItems: "center",
        marginTop: "4px",
        fontFamily: monoFont,
        fontSize: dimSize,
    };
    const optionField = {
        width: "100%",
        boxSizing: "border-box",
        margin: 0,
        fontFamily: monoFont,
    };
    const addOptionButton = e("button", {
        ref: function (el) {
            if (el && focusOptionKey.current === ADD_OPTION) {
                focusOptionKey.current = null;
                el.focus();
            }
        },
        onClick: addOption,
        disabled: running,
        title: "Add an option for the test",
        "aria-label": "Add option",
        className: iconButtonClass + " codicon-add",
        style: { ...iconButtonStyle(running), gridColumn: 5, justifySelf: "end" },
    });

    // The settings themselves, in a popup below the gear: the seed for property tests, the reason
    // for a rejected one, how the named results of a run first appear, and the test options.
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
                          outline: seedValid ? undefined : invalidOutline,
                      },
                  }),
              ),
              seedValid ? null : e("div", { style: hintStyle }, seedHint),
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
              // With no rows yet, the add button follows the heading.
              e(
                  "div",
                  { style: { ...settingRow, marginTop: "4px" } },
                  "Options:",
                  options.length ? null : addOptionButton,
              ),
              options.map(function (opt) {
                  // A row with a problem is marked, and Run waits for it to be fixed.
                  const nameValid = optionProblem(opt) === null;
                  return e(
                      "div",
                      {
                          key: opt.key,
                          role: "group",
                          "aria-label": "Option",
                          style: optionRow,
                      },
                      "--",
                      e("input", {
                          ref: function (el) {
                              if (el && focusOptionKey.current === opt.key) {
                                  focusOptionKey.current = null;
                                  el.focus();
                              }
                          },
                          type: "text",
                          value: opt.name,
                          placeholder: "name",
                          disabled: running,
                          title: "Option name",
                          "aria-invalid": !nameValid,
                          onChange: function (ev) {
                              editOption(opt.key, "name", ev.target.value);
                          },
                          style: {
                              ...optionField,
                              outline: nameValid ? undefined : invalidOutline,
                          },
                      }),
                      "=",
                      e("input", {
                          type: "text",
                          value: opt.value,
                          placeholder: "value",
                          disabled: running,
                          title: "Option value; blank for a flag",
                          onChange: function (ev) {
                              editOption(opt.key, "value", ev.target.value);
                          },
                          style: optionField,
                      }),
                      e("button", {
                          onClick: function () {
                              removeOption(opt.key);
                          },
                          disabled: running,
                          title: "Remove this option",
                          "aria-label": "Remove option",
                          className: iconButtonClass + " codicon-close",
                          style: { ...iconButtonStyle(running), justifySelf: "end" },
                      }),
                      unreadOptions.includes(opt.name.trim())
                          ? e("span", {
                                role: "img",
                                title: "The test never read this option in the last run",
                                "aria-label": "Never read",
                                className: "codicon codicon-warning",
                                style: { color: warningColor, justifySelf: "end" },
                            })
                          : null,
                  );
              }),
              // Below the rows, the add button sits in the column of their remove buttons.
              options.length ? e("div", { style: optionRow }, addOptionButton) : null,
              optionsValid ? null : e("div", { style: hintStyle }, optionsHint),
          )
        : null;

    const outcome = st.tag === "done" ? st.outcome : null;
    const timings = st.tag === "idle" ? null : st;
    const execStartTime = timings ? timings.execStartTime : 0;

    // The results the widget received, restored with the rest of a cached run, whose chunks have the
    // times the runner stamped on them. A run that reported no results, such as one whose build
    // failed, has only its outcome's.
    const liveResults = timings ? timings.results : [];
    // The whole run's output, in the order the test produced it, and the output of each result.
    const allChunks = timings ? timings.chunks : [];
    const outputs = outputsByResult(outputCache, allChunks);
    const results = (liveResults.length ? liveResults : resultsOfOutcome(outcome)).map(
        function (r) {
            const output = outputs.get(r.id);
            return output ? { ...r, output } : r;
        },
    );
    const kids = childrenOf(results);
    const failing = failingPaths(results);
    // What the test's own code reported, which is what the verdict line and the summary under it
    // show. The outcome's message is the innermost failure's, and that result reports it in the
    // tree itself, so taking it here as well would say it twice. The test's own result has a verdict
    // once the test has ended. A run that ended before that, such as one whose build failed or whose
    // runner exited early, has only the outcome to report.
    const own = results.length && results[0].status ? results[0] : null;
    const ownMessage = own ? own.message : (outcome && outcome.message) || "";
    const ownDetail = own ? own.detail : (outcome && outcome.detail) || "";
    const ownLocation = own ? own.location : (outcome && outcome.location) || null;
    const rootOutput = results.length ? results[0].output : [];
    // When the run's output is shown in more than one box, a control in the title copies all of it.
    const outputBoxes = results.filter(function (r) {
        return r.output.length > 0;
    }).length;
    const copyAll =
        outputBoxes > 1 && allChunks.length
            ? e(CopyAllButton, { key: "copy-all", chunks: allChunks })
            : null;
    // Keyed so it keeps its state when the message and detail blocks appear ahead of it.
    const outputSection = rootOutput.length
        ? e(OutputSection, {
              key: "output",
              chunks: rootOutput,
              // The output grows in place, so its length is what tells a new render apart.
              length: rootOutput.length,
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

    // Dimmed badges after the status: text, and for the seed and the options, a click that fills
    // the settings with them.
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
    if (outcome && outcome.options && outcome.options.length) {
        const optionsUsed = outcome.options;
        badges.push({
            text: "Options " + optionsCommandLine(optionsUsed),
            title: "Use these options for the next run",
            onClick: function () {
                repeatOptions(optionsUsed);
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
                  // The row is a flex, so an automatic left margin puts the control at its end.
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
    // An option that the test never read is most often a misspelled name.
    if (unreadOptions.length)
        extras.push(
            e(
                "div",
                { key: "unread", style: { color: warningColor, fontSize: dimSize } },
                (unreadOptions.length === 1 ? "option" : "options") +
                    " never read by this test: " +
                    unreadOptions.join(", "),
            ),
        );

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
    // The pointer arriving means Run may be next, so the file's state is checked at once.
    return e(
        "details",
        {
            open,
            onToggle: /** @param ev {React.SyntheticEvent<HTMLDetailsElement>} */ function (ev) {
                setOpen(ev.currentTarget.open);
            },
            onMouseEnter: checkFile,
        },
        e(
            "summary",
            { className: "mv2 pointer non-selectable" },
            "Errata test: ",
            e("span", { style: { fontFamily: monoFont, fontSize: "0.95em" } }, name),
            // The title's controls float at its right, where the goal sections keep theirs. A click
            // on one is the control's own, so it leaves the disclosure as it was.
            e(
                "span",
                {
                    className: "fr",
                    onClick: function (ev) {
                        ev.preventDefault();
                    },
                },
                copyAll,
                gearButton,
            ),
        ),
        settingsPopup,
        open ? e("div", { className: "ml1" }, header, body) : null,
    );
}
