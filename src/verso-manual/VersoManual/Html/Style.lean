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

#toc a {
    color: #333;
    text-decoration: none;
}

#toc a:hover {
    text-decoration: underline;
    color: #000;
}

#toc .split-tocs {
    padding-left: 0.5em;
    padding-right: 0.5em;
    margin-top: 1.5em;
}

#toc .split-toc.book {
    margin-bottom: 1.5em;
}

#toc .split-toc.book .title {
    font-weight: 600;
}

#toc .split-toc {
    margin-bottom: 1em;
    font-family: var(--verso-structure-font-family);
}


#toc .split-toc label.toggle-split-toc {
}

#toc .split-toc .title {
    display: flex;
    flex-wrap: nowrap;
}

#toc .split-toc label.toggle-split-toc input[type="checkbox"] {
    display: inline-block;
    position: absolute;
    top: 0;
    left: 0;
    opacity: 0;
    height: 0;
    width: 0;
    z-index: -10;
}

#toc .split-toc label.toggle-split-toc::before {
    width: 1em;
    height: 1em;
    display: inline-block;
    background-color: black;
    content: ' ';
    transition: ease 0.2s;
    margin-right: 0.5em;
    clip-path: polygon(100% 0, 0 0, 50% 100%);
    width: 0.6em;
    height: 0.6em;
}

#toc .split-toc label.toggle-split-toc:has(input[type="checkbox"]:not(:checked))::before {
  transform: rotate(-90deg);
}

#toc .split-toc > :not(:first-child) {
    max-height: 0px;
    display: block;
    overflow: hidden;
    transition: all 0.1s ease-in;
    margin-left: 0.25em;
}

#toc .split-toc:has(.toggle-split-toc input[type="checkbox"]:not(:checked)) > :not(:first-child) {
    padding: 0;
    margin: 0;
}

#toc .split-toc:has(.toggle-split-toc input[type="checkbox"]:checked) > :not(:first-child) {
    max-height: 100%;
}

#toc .split-toc table {
    border-left: 1px dotted;
    padding-left: 1.2em;
    padding-top: 0.2em;
}

#toc .split-toc tr {
    padding-top: 0.1em;
}

#toc .split-toc td {
    vertical-align: top;
    font-size: 90%;
}

#toc .split-toc .current td:not(.num) {
    text-decoration-line: underline;
    text-decoration-style: dotted;
}

#toc .split-toc td.num {
    font-variant-numeric: tabular-nums;
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
