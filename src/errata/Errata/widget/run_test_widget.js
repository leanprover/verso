// @ts-check
import * as React from "react";
import { useRpcSession } from "@leanprover/infoview";

const e = React.createElement;

// Persists the last outcome per test for the lifetime of the InfoView session, so leaving and
// returning to a test's `@[test]` marker shows its previous result rather than a blank widget.
const resultCache = new Map();

const STATUS_COLORS = {
    passed: "#2e7d32",
    failed: "#c62828",
    error: "#e65100",
    skipped: "#6b6b6b",
};

const STATUS_SYMBOLS = {
    passed: "✓",
    failed: "✗",
    error: "⚠",
    skipped: "○",
};

const STATUS_LABELS = {
    passed: "Passed",
    failed: "FAILED",
    error: "ERROR",
    skipped: "Skipped",
};

const preStyle = {
    margin: "4px 0 0 0",
    padding: "6px 8px",
    whiteSpace: "pre-wrap",
    wordBreak: "break-word",
    background: "var(--vscode-textCodeBlock-background, rgba(127,127,127,0.1))",
    borderRadius: "3px",
    fontSize: "12px",
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

const monoFont = "var(--vscode-editor-font-family, monospace)";

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

// Renders captured output: stdout and stderr interleaved in order, both in the editor's code font,
// with stderr italicized. Hovering a chunk highlights it and reports its stream and time offset.
function outputBlock(chunks, execStartTime, hovered, setHovered) {
    return e(
        "pre",
        {
            style: { ...preStyle, fontFamily: monoFont },
            onMouseLeave: function () {
                setHovered(null);
            },
        },
        ...chunks.map(function (c, i) {
            return e(
                "span",
                {
                    key: i,
                    title: chunkLabel(c, execStartTime),
                    onMouseEnter: function () {
                        setHovered(i);
                    },
                    style: {
                        fontStyle: c.stream === "stderr" ? "italic" : undefined,
                        borderRadius: "2px",
                        backgroundColor:
                            hovered === i
                                ? "var(--vscode-editor-hoverHighlightBackground, rgba(120,170,255,0.3))"
                                : undefined,
                    },
                },
                c.text,
            );
        }),
    );
}

/**
 * @typedef {{stream: string, text: string, time?: number}} Chunk
 * @typedef {{status: string, durationMs: number, message?: string, detail?: string,
 *            output?: Chunk[], description?: string}} Outcome
 * @typedef {{phase: string, chunks: Chunk[], startTime: number, buildMs: number,
 *            execStartTime: number}} RunFields
 *
 * The run's lifecycle as a single state, so that contradictory combinations (a verdict alongside
 * an error, a spinner alongside an outcome) cannot be represented:
 *
 *   idle       no run for this test, and no recorded outcome to show
 *   running    a run is in progress, streaming output
 *   done       a finished run's outcome (live or restored from the session cache)
 *   cancelled  the run was stopped before it produced an outcome
 *   failed     the run could not be carried out at all
 *
 * All timings come from the server, which records them per run: they survive the widget being
 * remounted while the run continues, and the server is on the same machine, so its clock agrees
 * with the client's.
 *
 * @typedef {{tag: "idle"}
 *   | ({tag: "running"} & RunFields)
 *   | ({tag: "done", outcome: Outcome} & RunFields)
 *   | {tag: "cancelled", chunks: Chunk[]}
 *   | {tag: "failed", error: string, chunks: Chunk[]}} RunUi
 */

/** @type {RunUi} */
const idleState = { tag: "idle" };

/**
 * A finished state showing a recorded outcome, with no live chunks or timings of its own.
 * @param outcome {Outcome}
 * @returns {RunUi}
 */
function doneState(outcome) {
    return {
        tag: "done",
        outcome,
        phase: "",
        chunks: [],
        startTime: 0,
        buildMs: 0,
        execStartTime: 0,
    };
}

/**
 * Steps the run state by one event:
 *
 *   reset    the cursor moved onto a (possibly different) test; show its cached outcome, if any
 *   start    the user started a run; the client's clock stands in for the start time until the
 *            server reports the authoritative one
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
        case "reset":
            return ev.outcome ? doneState(ev.outcome) : idleState;
        case "start":
            return {
                tag: "running",
                phase: "building",
                chunks: [],
                startTime: ev.now,
                buildMs: 0,
                execStartTime: 0,
            };
        case "server": {
            const res = ev.res;
            // Zero-valued fields in a reply mean "no news"; the server's values otherwise win.
            const prev =
                st.tag === "running"
                    ? st
                    : { phase: "running", chunks: [], startTime: 0, buildMs: 0, execStartTime: 0 };
            const merged = {
                phase: res.phase || prev.phase,
                chunks:
                    res.chunks && res.chunks.length ? prev.chunks.concat(res.chunks) : prev.chunks,
                startTime: res.startTime || prev.startTime,
                buildMs: res.buildMs || prev.buildMs,
                execStartTime: res.execStartTime || prev.execStartTime,
            };
            if (!res.done) return { tag: "running", ...merged };
            if (res.outcome) return { tag: "done", outcome: res.outcome, ...merged };
            // Done without an outcome: nothing is running server-side. That ends a watched run
            // (stopped from elsewhere, or its process died); in any other state it is no news.
            return st.tag === "running" ? { tag: "cancelled", chunks: st.chunks } : st;
        }
        case "cancel":
            return { tag: "cancelled", chunks: st.tag === "running" ? st.chunks : [] };
        case "fail":
            return {
                tag: "failed",
                error: ev.error,
                chunks: st.tag === "running" ? st.chunks : [],
            };
        default:
            return st;
    }
}

export default function (props) {
    const rs = useRpcSession();
    // Keyed by both the test and a hash of its source, so editing the test changes the key and
    // invalidates its cached/in-progress run.
    const version = props.version || "";
    const cacheKey = JSON.stringify(props.decl) + "@" + version;

    const [st, dispatch] = React.useReducer(step, undefined, function () {
        const cached = resultCache.get(cacheKey);
        return cached ? doneState(cached) : idleState;
    });
    // Milliseconds since the run started, ticking while it does.
    const [elapsed, setElapsed] = React.useState(0);
    // The output chunk under the cursor, highlighted with its timestamp shown.
    const [hovered, setHovered] = React.useState(null);
    // Whether the file has no unsaved changes; the test runs the saved version, so Run is gated on it.
    const [clean, setClean] = React.useState(true);
    // Briefly true after the output is copied, to confirm the copy in the button label.
    const [copied, setCopied] = React.useState(false);
    // Whether the output disclosure is expanded; open by default, collapsible to hide large output.
    const [outputOpen, setOutputOpen] = React.useState(true);
    // Whether the cursor is over the output area, revealing the floating copy button.
    const [overOutput, setOverOutput] = React.useState(false);

    // Bumped on each run start, cancel, and unmount so a superseded await loop ignores late replies.
    const gen = React.useRef(0);
    // The number of chunks already pulled from the server, so a reconnect replays from the start.
    const sinceRef = React.useRef(0);
    // The last phase the widget saw; "" forces the next await to return the run's current phase at once.
    const phaseRef = React.useRef("");

    const running = st.tag === "running";
    const runStart = running ? st.startTime : 0;

    React.useEffect(
        function () {
            if (!running || !runStart) return undefined;
            function update() {
                setElapsed(Math.max(0, Date.now() - runStart));
            }
            update();
            const timer = setInterval(update, 100);
            return function () {
                clearInterval(timer);
            };
        },
        [running, runStart],
    );

    function loop(myGen) {
        rs.call("Errata.Widget.awaitOutput", {
            decl: props.decl,
            since: sinceRef.current,
            version: version,
            phase: phaseRef.current,
        }).then(
            function (res) {
                if (gen.current !== myGen) return;
                if (res.phase) phaseRef.current = res.phase;
                if (res.chunks && res.chunks.length) sinceRef.current = res.nextSince;
                if (res.done && res.outcome) resultCache.set(cacheKey, res.outcome);
                dispatch({ type: "server", res: res });
                if (!res.done) loop(myGen);
            },
            function (err) {
                if (gen.current !== myGen) return;
                dispatch({ type: "fail", error: (err && err.message) || String(err) });
            },
        );
    }

    // The InfoView reuses one component instance for whichever test the cursor is on, so reset and
    // reconnect whenever the test changes (keyed on `cacheKey`), not just on mount. Restores any cached
    // outcome for this test and replays an in-progress run from the start.
    React.useEffect(
        function () {
            const myGen = gen.current + 1;
            gen.current = myGen;
            sinceRef.current = 0;
            phaseRef.current = "";
            dispatch({ type: "reset", outcome: resultCache.get(cacheKey) || null });
            setHovered(null);
            loop(myGen);
            let cancelledCheck = false;
            let cleanTimer = null;
            function checkClean() {
                rs.call("Errata.Widget.bufferClean", { decl: props.decl }).then(
                    function (c) {
                        if (cancelledCheck) return;
                        setClean(c);
                        // While the buffer is dirty, re-check so the button re-enables shortly after a save.
                        if (!c) cleanTimer = setTimeout(checkClean, 1500);
                    },
                    function () {},
                );
            }
            checkClean();
            return function () {
                gen.current += 1;
                cancelledCheck = true;
                if (cleanTimer) clearTimeout(cleanTimer);
            };
        },
        [cacheKey],
    );

    function run() {
        const myGen = gen.current + 1;
        gen.current = myGen;
        sinceRef.current = 0;
        phaseRef.current = "building";
        dispatch({ type: "start", now: Date.now() });
        setElapsed(0);
        rs.call("Errata.Widget.startTest", {
            decl: props.decl,
            module: props.module,
            version: version,
        }).then(
            function () {
                if (gen.current === myGen) loop(myGen);
            },
            function (err) {
                if (gen.current !== myGen) return;
                dispatch({ type: "fail", error: (err && err.message) || String(err) });
            },
        );
    }

    function cancel() {
        gen.current += 1;
        dispatch({ type: "cancel" });
        rs.call("Errata.Widget.cancelTest", { decl: props.decl }).catch(function () {});
    }

    const name = props.name || "test";

    const header = e(
        "div",
        { style: { display: "flex", alignItems: "center", gap: "8px" } },
        running
            ? e("button", { onClick: cancel }, "Cancel")
            : e(
                  "button",
                  {
                      onClick: run,
                      disabled: !clean,
                      title: clean ? undefined : "Save the file to run the test",
                  },
                  st.tag === "idle" ? "Run" : "Run again",
              ),
        e(
            "span",
            {
                style: {
                    fontFamily: "var(--vscode-editor-font-family, monospace)",
                    fontSize: "12px",
                },
            },
            name,
        ),
        !clean && !running
            ? e("span", { style: { opacity: 0.6, fontSize: "11px" } }, "unsaved — save to run")
            : null,
    );

    const outcome = st.tag === "done" ? st.outcome : null;
    const timings = st.tag === "running" || st.tag === "done" ? st : null;
    const execStartTime = timings ? timings.execStartTime : 0;

    // Prefer the live, server-timestamped chunks; fall back to a cached outcome's output.
    const liveChunks = st.tag === "idle" ? [] : st.chunks;
    const chunks = liveChunks.length ? liveChunks : outcome && outcome.output ? outcome.output : [];

    function copyOutput() {
        const text = chunks
            .map(function (c) {
                return c.text;
            })
            .join("");
        Promise.resolve(navigator.clipboard.writeText(text)).then(
            function () {
                setCopied(true);
                setTimeout(function () {
                    setCopied(false);
                }, 1500);
            },
            function () {},
        );
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

    // A copy button floating over the top-right of the output, revealed on hover (or while confirming).
    const copyButton = e(
        "button",
        {
            onClick: copyOutput,
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
                opacity: overOutput || copied ? 0.95 : 0,
                transition: "opacity 0.1s",
            },
        },
        copyIcon,
    );

    const outputSection =
        chunks.length === 0
            ? null
            : e(
                  "details",
                  {
                      key: "output",
                      open: outputOpen,
                      onToggle: /** @param ev {React.ToggleEvent<HTMLDetailsElement>} */ function (
                          ev,
                      ) {
                          setOutputOpen(ev.currentTarget.open);
                      },
                      style: { marginTop: "4px" },
                  },
                  e(
                      "summary",
                      { style: { opacity: 0.7, fontSize: "11px", cursor: "pointer" } },
                      hovered !== null && chunks[hovered]
                          ? [
                                "Output  —  ",
                                e(
                                    "span",
                                    { key: "stream", style: { fontFamily: monoFont } },
                                    chunks[hovered].stream,
                                ),
                                " " + chunkOffset(chunks[hovered], execStartTime),
                            ]
                          : "Output",
                  ),
                  e(
                      "div",
                      {
                          style: { position: "relative" },
                          onMouseEnter: function () {
                              setOverOutput(true);
                          },
                          onMouseLeave: function () {
                              setOverOutput(false);
                          },
                      },
                      copyButton,
                      outputBlock(chunks, execStartTime, hovered, setHovered),
                  ),
              );

    // The primary status/progress element, then dimmed badges: start time, build and run durations.
    let primary = null;
    if (st.tag === "running") {
        const label = st.phase === "building" ? "Building… " : "Running… ";
        primary = e(
            "span",
            { style: { opacity: 0.8 } },
            label,
            e("span", { style: { fontFamily: monoFont } }, formatDuration(elapsed)),
        );
    } else if (st.tag === "failed") {
        primary = e(
            "span",
            { style: { color: STATUS_COLORS.error } },
            "could not run: " + st.error,
        );
    } else if (st.tag === "done") {
        primary = e(
            "span",
            { style: { color: STATUS_COLORS[st.outcome.status] || "inherit", fontWeight: 600 } },
            (STATUS_SYMBOLS[st.outcome.status] || "") +
                " " +
                (STATUS_LABELS[st.outcome.status] || st.outcome.status),
        );
    } else if (st.tag === "cancelled") {
        primary = e("span", { style: { opacity: 0.7 } }, "cancelled");
    }

    const badges = [];
    if (timings && timings.startTime) badges.push("Start " + formatClock(timings.startTime));
    if (timings && timings.buildMs) badges.push("Build " + formatDuration(timings.buildMs));
    if (outcome) badges.push("Run " + formatDuration(outcome.durationMs));

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
                  ...badges.map(function (b, i) {
                      return e(
                          "span",
                          { key: i, style: { opacity: 0.55, fontSize: "11px" } },
                          "· " + b,
                      );
                  }),
              )
            : null;

    const extras = [];
    if (outcome && outcome.message) extras.push(e("div", { key: "msg" }, block(outcome.message)));
    if (outcome && outcome.detail) extras.push(e("div", { key: "detail" }, block(outcome.detail)));

    // The test's docstring, rendered by Lean to Markdown and shown as text alongside its result.
    const descriptionSection =
        outcome && outcome.description
            ? e(
                  "div",
                  {
                      key: "description",
                      style: {
                          marginTop: "4px",
                          fontSize: "12px",
                          opacity: 0.85,
                          whiteSpace: "pre-wrap",
                      },
                  },
                  outcome.description,
              )
            : null;

    const body =
        infoRow || descriptionSection || extras.length || outputSection
            ? e(
                  "div",
                  { style: { marginTop: "4px" } },
                  infoRow,
                  descriptionSection,
                  ...extras,
                  outputSection,
              )
            : null;

    return e("div", { style: { padding: "2px 0" } }, header, body);
}
