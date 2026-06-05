import * as React from "react";

const e = React.createElement;

function swatch(css, size) {
    return e("span", {
        style: {
            display: "inline-block",
            width: size,
            height: size,
            borderRadius: "3px",
            border: "1px solid rgba(0, 0, 0, 0.25)",
            backgroundColor: css,
            verticalAlign: "middle",
        },
    });
}

function cvdRow(label, css) {
    return e(
        "div",
        { style: { display: "flex", alignItems: "center", gap: "0.4em", padding: "0.1em 0.4em" } },
        swatch(css, "1em"),
        e("span", { style: { fontSize: "0.85em" } }, label),
        e("code", { style: { fontSize: "0.8em", opacity: 0.7 } }, css),
    );
}

// A read-only preview of a `color%` literal: the color itself, plus how it looks under each of the
// three dichromacies. All CSS strings are pre-rendered by the `colorLit` elaborator.
export default function (props) {
    const main = e(
        "div",
        { style: { padding: "0.4em" } },
        swatch(props.css, "1.4em"),
        e("code", { style: { marginLeft: "0.5em", verticalAlign: "middle" } }, props.css),
    );
    const cvd = e(
        "div",
        {
            style: {
                borderTop: "1px solid rgba(0, 0, 0, 0.1)",
                marginTop: "0.3em",
                paddingTop: "0.2em",
            },
        },
        e(
            "div",
            { style: { fontSize: "0.75em", opacity: 0.6, padding: "0 0.4em 0.1em" } },
            "Simulated color vision differences",
        ),
        cvdRow("Protanopia", props.protanopia),
        cvdRow("Deuteranopia", props.deuteranopia),
        cvdRow("Tritanopia", props.tritanopia),
    );
    return e("div", {}, main, cvd);
}
