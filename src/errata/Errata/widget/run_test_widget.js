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

export default function (props) {
    const rs = useRpcSession();
    // Keyed by both the test and a hash of its source, so editing the test changes the key and
    // invalidates its cached/in-progress run.
    const version = props.version || "";
    const cacheKey = JSON.stringify(props.decl) + "@" + version;

    const [outcome, setOutcome] = React.useState(() => resultCache.get(cacheKey) || null);
    const [running, setRunning] = React.useState(false);
    const [cancelled, setCancelled] = React.useState(false);
    const [elapsed, setElapsed] = React.useState(0);
    const [error, setError] = React.useState(null);
    const [live, setLive] = React.useState([]);
    const [phase, setPhase] = React.useState("running");
    // When the run started (epoch ms), recorded server-side so it survives a reconnect.
    const [startTime, setStartTime] = React.useState(0);
    // How long the build took (ms), and when the test body started (epoch ms) for output offsets.
    const [buildMs, setBuildMs] = React.useState(0);
    const [execStartTime, setExecStartTime] = React.useState(0);
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
    const liveRef = React.useRef([]);
    // The number of chunks already pulled from the server, so a reconnect replays from the start.
    const sinceRef = React.useRef(0);
    // The last phase the widget saw; "" forces the next await to return the run's current phase at once.
    const phaseRef = React.useRef("");
    const startedAt = React.useRef(0);

    React.useEffect(
        function () {
            if (!running) return undefined;
            const timer = setInterval(function () {
                setElapsed(Date.now() - startedAt.current);
            }, 100);
            return function () {
                clearInterval(timer);
            };
        },
        [running],
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
                if (res.startTime) setStartTime(res.startTime);
                if (res.buildMs) setBuildMs(res.buildMs);
                if (res.execStartTime) setExecStartTime(res.execStartTime);
                if (res.phase) {
                    setPhase(res.phase);
                    phaseRef.current = res.phase;
                }
                if (res.chunks && res.chunks.length) {
                    liveRef.current = liveRef.current.concat(res.chunks);
                    setLive(liveRef.current);
                    sinceRef.current = res.nextSince;
                    setRunning(true);
                }
                if (res.done) {
                    if (res.outcome) {
                        resultCache.set(cacheKey, res.outcome);
                        setOutcome(res.outcome);
                    }
                    setRunning(false);
                    return;
                }
                setRunning(true);
                loop(myGen);
            },
            function (err) {
                if (gen.current !== myGen) return;
                setError((err && err.message) || String(err));
                setRunning(false);
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
            liveRef.current = [];
            setLive([]);
            setOutcome(resultCache.get(cacheKey) || null);
            setRunning(false);
            setCancelled(false);
            setError(null);
            setPhase("running");
            setStartTime(0);
            setBuildMs(0);
            setExecStartTime(0);
            setHovered(null);
            startedAt.current = Date.now();
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
        liveRef.current = [];
        setLive([]);
        sinceRef.current = 0;
        setOutcome(null);
        setError(null);
        setCancelled(false);
        setPhase("building");
        phaseRef.current = "building";
        startedAt.current = Date.now();
        setElapsed(0);
        setRunning(true);
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
                setError((err && err.message) || String(err));
                setRunning(false);
            },
        );
    }

    function cancel() {
        gen.current += 1;
        setRunning(false);
        setCancelled(true);
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
                  outcome || error || cancelled ? "Run again" : "Run",
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

    // Prefer the live, server-timestamped chunks; fall back to a cached outcome's output.
    const chunks = live.length ? live : outcome && outcome.output ? outcome.output : [];

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
                      onToggle: function (ev) {
                          setOutputOpen(ev.target.open);
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
    if (running) {
        const label = phase === "building" ? "Building… " : "Running… ";
        primary = e(
            "span",
            { style: { opacity: 0.8 } },
            label,
            e("span", { style: { fontFamily: monoFont } }, formatDuration(elapsed)),
        );
    } else if (error) {
        primary = e("span", { style: { color: STATUS_COLORS.error } }, "could not run: " + error);
    } else if (outcome) {
        primary = e(
            "span",
            { style: { color: STATUS_COLORS[outcome.status] || "inherit", fontWeight: 600 } },
            (STATUS_SYMBOLS[outcome.status] || "") +
                " " +
                (STATUS_LABELS[outcome.status] || outcome.status),
        );
    } else if (cancelled) {
        primary = e("span", { style: { opacity: 0.7 } }, "cancelled");
    }

    const badges = [];
    if (startTime) badges.push("Start " + formatClock(startTime));
    if (buildMs) badges.push("Build " + formatDuration(buildMs));
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
