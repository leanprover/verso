import * as React from "react";

const e = React.createElement;

// A read-only preview of a `color%` literal: a swatch filled with the color next to its CSS
// rendering. The pre-rendered CSS string is supplied as `props.css` by the `colorLit` elaborator.
export default function (props) {
  const swatch = e("span", {
    style: {
      display: "inline-block",
      width: "1.4em",
      height: "1.4em",
      borderRadius: "3px",
      border: "1px solid rgba(0, 0, 0, 0.25)",
      backgroundColor: props.css,
      verticalAlign: "middle",
    },
  });
  const label = e(
    "code",
    { style: { marginLeft: "0.5em", verticalAlign: "middle" } },
    props.css,
  );
  return e("div", { style: { padding: "0.4em" } }, swatch, label);
}
