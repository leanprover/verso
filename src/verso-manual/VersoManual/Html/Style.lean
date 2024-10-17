/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

namespace Verso.Genre.Manual.Html.Css

def pageStyle : String := r####"
/******** Customizability ********/

:root {
    --verso-structure-font-family: "Helvetica Neue","Segoe UI",Arial,sans-serif;
    --verso-text-font-family: Georgia, Times, "Times New Roman", serif;
    --verso-code-font-family: monospace;
    --verso-content-max-width: 45em;
    --verso-toc-background-color: #fafafa;
}

/******** Reset ********/

body {
    margin: 0;
    padding: 0;
}

/******** Theme ********/

h1, h2, h3, h4, h5, h6 {
    font-family: var(--verso-structure-font-family);
    text-rendering: optimizeLegibility;
    margin-top: 1.5rem;
}

p, dt, dd {
    font-family: var(--verso-text-font-family);
}

dt {
    font-weight: bold;
}

dd > p:first-child {
    margin-top: 0;
}

pre, code {
    font-family: var(--verso-code-font-family);
    font-variant-ligatures: none;
}

/******** Page Layout ********/

.with-toc {
    display: grid;
    grid-template-columns: min-content auto;
    grid-template-rows: min-content 1fr;
    grid-template-areas:
        "toc header"
        "toc text";
    height: 100vh;
    overflow: hidden;
}

.with-toc #toc {
    overflow-y: auto;
    grid-area: toc;
    height: 100vh;
}

.with-toc > header {
    grid-area: header;
}

.with-toc > main {
    grid-area: text;
    overflow-y: auto;
}

/******** Table of Contents ********/

#toc {
    width: 0em;
    transition: 0.4s;
    background-color: var(--verso-toc-background-color);
}

#toc:has(>#toggle-toc:checked) {
    width: 15em;
}

#toc #toggle-toc {
    display: none;
}

#toc ol {
    padding-left: 0.5em;
}

#toc ol li {
    list-style-type: none;
    font-family: var(--verso-structure-font-family);
    font-size: 12px;
    padding: 0;
}

#toc > ol > li {
    margin-left: 1.5em;
    position: relative;
    margin-bottom: 1ex;
}

#toc > ol > li > a > .number, #toc > ol > li > a > .unnumbered {
    width: 1.5em;
    position: absolute;
    left: -1.5em;
    box-sizing: border-box;
    font-variant-numeric: tabular-nums;
}

#toc > ol > li > ol > li {
    margin-left: 2.25em;
    position: relative;
    margin-bottom: 0.5ex;
}

#toc > ol > li > ol > li > a > .number, #toc > ol > li > ol > li > a > .unnumbered {
  width: 2.25em;
  position: absolute;
  left: -2.25em;
  box-sizing: border-box;
  font-variant-numeric: tabular-nums;
}


#toc > ol > li > ol > li > a > .number, #toc > ol > li > ol > li > a > .unnumbered {
  width: 2.25em;
  position: absolute;
  left: -2.25em;
  box-sizing: border-box;
  font-variant-numeric: tabular-nums;
}

#toc > ol > li > ol > li > ol > li > a > .number, #toc > ol > li > ol > li > ol > li > a > .unnumbered {
    width: 3.5em;
    position: absolute;
    left: -3.5em;
    box-sizing: border-box;
    font-variant-numeric: tabular-nums;
}

#toc > ol > li > ol > li > ol > li {
    margin-left: 3.5em;
    position: relative;
}


#toc a {
    color: #333;
    text-decoration: none;
}

#toc a:hover {
    text-decoration: underline;
    color: #000;
}

/******** Headerline ********/

header {
    display: grid;
    grid-template-columns: 1fr auto 1fr;
    grid-template-areas: "controls pagetitle print";
    align-items: center;
}

header h1 {
    margin-top: 0.2em;
    margin-bottom: 0.2em;
    text-align: center;
    grid-area: pagetitle;
    font-size: 1.25em;
}

header h1 a, header h1 a:link, header h1 a:visited {
    text-decoration: inherit;
    color: inherit;
}

header h1 a:hover {
    text-decoration: underline;
}

header #controls {
    grid-area: controls;
}

header #print {
    grid-area: print;
    text-align: right;
}

header #print > *, header #controls > * {
    height: 3em;
    width: 3em;
    line-height: 3em;
    display: inline-block;
    text-align: center;
    vertical-align: center;
}


header #toggle-toc-click {
    cursor: pointer;
}

/******** Text ********/

main .titlepage h1 {
    text-align: center;
}

main .authors {
    text-align: center;
}

main > section {
    margin: auto;
}

main section {
    max-width: var(--verso-content-max-width);
}

main ol.section-toc, main .section-toc ol {
    list-style-type: none;
}

main ol.section-toc {
    padding-left: 0;
}

main .section-toc > li {
    padding-bottom: 0.25em;
}

main .section-toc ol {
    padding-left: 0.5em
}

main .section-toc li {
    font-weight: bold;
    font-family: var(--verso-structure-font-family);
    margin-left: 1em;
}

main .section-toc a, main .section-toc a:visited {
    color: inherit;
    text-decoration: none;
}

main .section-toc a:hover {
    text-decoration: underline;
}
"####
