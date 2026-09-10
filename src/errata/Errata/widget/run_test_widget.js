// @ts-check
import * as React from "react";
import {
    EditorContext,
    EnvPosContext,
    Markdown,
    useClientNotificationEffect,
    useEvent,
    useRpcSession,
} from "@leanprover/infoview";

const e = React.createElement;

// The last settled outcome of each test, keyed by its declaration and tagged with the source
// version that produced it, for the lifetime of the InfoView session. Leaving and returning to a
// test's `@[test]` marker shows its previous result again.
const resultCache = new Map();

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

// The message of a rejected RPC call.
function errorMessage(err) {
    return (err && err.message) || String(err);
}

const monoFont = "var(--vscode-editor-font-family, monospace)";

// The editor theme's colour for secondary text: the badges, hints, and the output summary. The
// theme keeps it legible against the panel's background, which dimming the foreground would not.
const dimColor = "var(--vscode-descriptionForeground, #717171)";

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
                props.onHover(c);
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

// Renders captured output: stdout and stderr interleaved in order. Hovering a chunk highlights it
// and reports its stream and time offset.
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
            return e(ChunkSpan, {
                key: i,
                chunk: c,
                execStartTime,
                hovered: hovered === c,
                onHover: setHovered,
            });
        }),
    );
}

// The collapsible output disclosure: a summary naming the hovered chunk's stream and time offset,
// the interleaved chunks, and a copy button floating over the output, revealed on hover. Whether
// it is open belongs to the caller, so a collapse outlasts the output being replaced.
const OutputSection = React.memo(function OutputSection(props) {
    const chunks = props.chunks;
    const execStartTime = props.execStartTime;
    // The output chunk under the cursor, highlighted with its timestamp shown. Held by identity,
    // so it matches only a chunk of the output currently shown.
    const [hovered, setHovered] = React.useState(null);
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

    function copyOutput() {
        const text = chunks
            .map(function (c) {
                return c.text;
            })
            .join("");
        Promise.resolve(navigator.clipboard.writeText(text)).then(
            function () {
                setCopied(true);
                if (copiedTimer.current) clearTimeout(copiedTimer.current);
                copiedTimer.current = setTimeout(function () {
                    copiedTimer.current = null;
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
            { style: { color: dimColor, fontSize: "11px", cursor: "pointer" } },
            hovered && chunks.includes(hovered)
                ? [
                      "Output  —  ",
                      e("span", { key: "stream", style: { fontFamily: monoFont } }, hovered.stream),
                      " " + chunkOffset(hovered, execStartTime),
                  ]
                : "Output",
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
            outputBlock(chunks, execStartTime, hovered, setHovered),
        ),
    );
});

/**
 * @typedef {{stream: string, text: string, time?: number}} Chunk
 * @typedef {{status: string, durationMs: number, message?: string, detail?: string,
 *            output?: Chunk[], description?: string, seed?: number}} Outcome
 * @typedef {{phase: string, chunks: Chunk[], startTime: number, startedAt: number,
 *            buildMs: number, execStartTime: number}} RunFields
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
    return { phase: "", chunks: [], startTime: 0, startedAt: 0, buildMs: 0, execStartTime: 0 };
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
            const merged = {
                phase: res.phase || prev.phase,
                chunks:
                    res.chunks && res.chunks.length ? prev.chunks.concat(res.chunks) : prev.chunks,
                startTime: res.startTime || prev.startTime,
                startedAt: res.elapsedMs ? ev.now - res.elapsedMs : prev.startedAt,
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
    // The seed for property tests as typed, or blank to have one drawn.
    const [seed, setSeed] = React.useState("");
    // Whether the run settings (the seed field) are shown, behind the gear button.
    const [settingsOpen, setSettingsOpen] = React.useState(false);
    // Whether the output disclosure is expanded; open by default, collapsible to hide large output.
    const [outputOpen, setOutputOpen] = React.useState(true);
    // Whether the widget's own disclosure is expanded, alongside the InfoView's other sections.
    const [panelOpen, setPanelOpen] = React.useState(true);
    // Bumped when the language server restarts, so the widget connects again through its new session.
    const [epoch, setEpoch] = React.useState(0);

    // The RPC session, which the InfoView replaces on every cursor move and after a server restart.
    // Calls go through the latest one, while the connection to the run is made once per mount and
    // once per restart.
    const rsRef = React.useRef(rs);
    React.useEffect(function () {
        rsRef.current = rs;
    });
    // Bumped on each run start, cancel, and disconnect so a superseded await loop ignores late replies.
    const gen = React.useRef(0);
    // The position past the chunks already received, from the server's last reply.
    const sinceRef = React.useRef(0);
    // The last phase the widget saw; "" forces the next await to return the run's current phase at once.
    const phaseRef = React.useRef("");
    // Whether the widget is connected, so late clean-check replies are dropped.
    const alive = React.useRef(false);
    // The pending re-check while the buffer is dirty, so a fresh check replaces it.
    const cleanTimer = React.useRef(null);
    // Bumped on each edit and each clean check, so a check begun before an edit reports nothing.
    const cleanGen = React.useRef(0);
    // The file this widget belongs to, from the InfoView's position context.
    const envPos = React.useContext(EnvPosContext);
    const uri = envPos ? envPos.uri : null;

    const running = st.tag === "running";
    const starting = st.tag === "running" && st.phase === "starting";

    // Asks the server whether the buffer is saved. While it is dirty, asks again every 1.5 s so
    // the button re-enables shortly after a save.
    function checkClean() {
        if (cleanTimer.current) {
            clearTimeout(cleanTimer.current);
            cleanTimer.current = null;
        }
        const myGen = cleanGen.current + 1;
        cleanGen.current = myGen;
        rsRef.current.call("Errata.Widget.bufferClean", { decl: props.decl }).then(
            function (c) {
                if (!alive.current || cleanGen.current !== myGen) return;
                setClean(c);
                if (!c) cleanTimer.current = setTimeout(checkClean, 1500);
            },
            function () {},
        );
    }

    // An edit to this file means the buffer is dirty. The retry then finds out when it is saved.
    useClientNotificationEffect(
        "textDocument/didChange",
        function (params) {
            if (params.textDocument.uri !== uri) return;
            cleanGen.current += 1;
            setClean(false);
            if (cleanTimer.current) clearTimeout(cleanTimer.current);
            cleanTimer.current = setTimeout(checkClean, 1500);
        },
        [uri],
    );

    function loop(myGen) {
        rsRef.current
            .call("Errata.Widget.awaitOutput", {
                decl: props.decl,
                since: sinceRef.current,
                version: version,
                phase: phaseRef.current,
            })
            .then(
                function (res) {
                    if (gen.current !== myGen) return;
                    if (res.phase) phaseRef.current = res.phase;
                    sinceRef.current = res.nextSince || 0;
                    dispatch({ type: "server", res: res, now: Date.now() });
                    if (!res.done) loop(myGen);
                },
                function (err) {
                    if (gen.current !== myGen) return;
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
            phaseRef.current = "";
            loop(myGen);
            alive.current = true;
            checkClean();
            return function () {
                gen.current += 1;
                alive.current = false;
                if (cleanTimer.current) clearTimeout(cleanTimer.current);
                cleanTimer.current = null;
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
            if (st.tag === "done") resultCache.set(declKey, { version, outcome: st.outcome });
            else if (st.tag !== "idle") resultCache.delete(declKey);
        },
        [st],
    );

    const seedText = seed.trim();
    const seedSet = seedText !== "";
    // A blank seed has one drawn; otherwise it must be a natural number that JSON carries exactly.
    const seedValid =
        !seedSet || (/^\d+$/.test(seedText) && Number.isSafeInteger(Number(seedText)));
    const seedHint = "The seed must be a natural number below 2^53";

    function run() {
        const myGen = gen.current + 1;
        gen.current = myGen;
        sinceRef.current = 0;
        phaseRef.current = "building";
        dispatch({ type: "start", now: Date.now() });
        const request = {
            decl: props.decl,
            module: props.module,
            version: version,
        };
        if (seedSet) request.seed = Number(seedText);
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
                checkClean();
            },
        );
    }

    function cancel() {
        gen.current += 1;
        dispatch({ type: "cancel" });
        rsRef.current.call("Errata.Widget.cancelTest", { decl: props.decl }).catch(function () {});
    }

    const name = props.name || "test";

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
        !clean && !running
            ? e("span", { style: { color: dimColor, fontSize: "11px" } }, "unsaved — save to run")
            : null,
    );

    // The run settings float at the right of the title, where the goal sections keep theirs: the
    // seed field when shown, then the gear that shows it. A click here is the control's own, so it
    // leaves the disclosure as it was.
    const runSettings = e(
        "span",
        {
            className: "fr",
            onClick: function (ev) {
                ev.preventDefault();
            },
        },
        settingsOpen
            ? e("input", {
                  type: "text",
                  inputMode: "numeric",
                  value: seed,
                  placeholder: "seed",
                  disabled: running,
                  title: seedValid ? "Seed for property tests; blank draws one" : seedHint,
                  "aria-label": "Seed for property tests",
                  "aria-invalid": !seedValid,
                  onChange: function (ev) {
                      setSeed(ev.target.value);
                  },
                  // Fits its value or placeholder; `size` stands in where `field-sizing` is
                  // unsupported.
                  size: Math.max(seed.length, 4) + 1,
                  style: {
                      fieldSizing: "content",
                      minWidth: "5ch",
                      fontFamily: monoFont,
                      fontSize: "11px",
                      // The title suppresses selection, which the field needs back.
                      userSelect: "text",
                      outline: seedValid
                          ? undefined
                          : "1px solid var(--vscode-inputValidation-errorBorder, #be1100)",
                  },
              })
            : null,
        e("button", {
            onClick: function () {
                setSettingsOpen(!settingsOpen);
            },
            title: settingsOpen
                ? "Hide run settings"
                : seedSet
                  ? "Run settings (seed " + seedText + ")"
                  : "Run settings",
            "aria-label": "Run settings",
            "aria-expanded": settingsOpen,
            className: "link pointer dim mh2 codicon codicon-settings-gear",
            style: {
                background: "none",
                border: "none",
                padding: 0,
                color: "var(--vscode-textLink-foreground, #0078d4)",
            },
        }),
    );

    const outcome = st.tag === "done" ? st.outcome : null;
    const timings = st.tag === "idle" ? null : st;
    const execStartTime = timings ? timings.execStartTime : 0;

    // Prefer the live, server-timestamped chunks; fall back to a cached outcome's output.
    const liveChunks = timings ? timings.chunks : [];
    const chunks = liveChunks.length ? liveChunks : outcome && outcome.output ? outcome.output : [];
    // Keyed so it keeps its state when the message and detail blocks appear ahead of it.
    const outputSection = chunks.length
        ? e(OutputSection, {
              key: "output",
              chunks,
              execStartTime,
              open: outputOpen,
              onOpenChange: setOutputOpen,
          })
        : null;

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
        primary = e(
            "span",
            { style: { color: "var(--vscode-errorForeground, #c62828)" } },
            "could not run: " + st.error,
        );
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
    if (outcome && typeof outcome.seed === "number") {
        const seedUsed = outcome.seed;
        badges.push({ text: "Run " + formatDuration(outcome.durationMs) });
        badges.push({
            text: "Seed " + seedUsed,
            title: "Use this seed for the next run",
            onClick: function () {
                setSeed(String(seedUsed));
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
                          { key: i, style: { color: dimColor, fontSize: "11px" } },
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
              )
            : null;

    const extras = [];
    if (outcome && outcome.message) extras.push(e("div", { key: "msg" }, block(outcome.message)));
    if (outcome && outcome.detail) extras.push(e("div", { key: "detail" }, block(outcome.detail)));

    // The test's docstring, rendered from the Markdown Lean produced for it, alongside its result.
    const descriptionSection =
        outcome && outcome.description
            ? e(
                  "div",
                  {
                      key: "description",
                      style: { marginTop: "4px", fontSize: "12px" },
                  },
                  e(Markdown, { contents: outcome.description }),
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

    // A disclosure in the InfoView's own style, so the test sits among the goal and message
    // sections. Its content is dropped while collapsed, as those sections do, so a long-running
    // test's output costs nothing to keep out of sight.
    //
    // While the buffer is dirty, the pointer arriving means Run may be next, so the saved state is
    // checked at once.
    return e(
        "details",
        {
            open: panelOpen,
            onToggle: /** @param ev {React.ToggleEvent<HTMLDetailsElement>} */ function (ev) {
                setPanelOpen(ev.currentTarget.open);
            },
            onMouseEnter: clean ? undefined : checkClean,
        },
        e(
            "summary",
            { className: "mv2 pointer non-selectable" },
            "Errata test: ",
            e("span", { style: { fontFamily: monoFont, fontSize: "12px" } }, name),
            runSettings,
        ),
        panelOpen ? e("div", { className: "ml1" }, header, body) : null,
    );
}
