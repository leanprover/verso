/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

namespace Verso.Genre.Manual.Html.Css

def pageStyle : String := r####"
/******** Customizability ********/

:root {
    /** Typography **/
    /* The font family used for headers, ToC entries, etc */
    --verso-structure-font-family: "Helvetica Neue","Segoe UI",Arial,sans-serif;
    /* The font family used for body text */
    --verso-text-font-family: Georgia, Times, "Times New Roman", serif;
    /* The font family used for code */
    --verso-code-font-family: monospace;
    /* What's the maximum line width, for legibility? */
    --verso-content-max-width: 45em;

    /** Table of Contents appearance **/
    --verso-toc-background-color: #fafafa;
    --verso-toc-text-color: black;

    /* How long should the ToC animation take? */
    --verso-toc-transition-time: 0.4s;

    /** Variables that control the “burger menu” appearance **/
    --verso-burger-height: 1.25em;
    --verso-burger-width: 1.25em;
    --verso-burger-line-width: 0.2em;
    --verso-burger-line-radius: 0.2em;
    --verso-burger-toc-visible-color: var(--verso-toc-text-color);
    --verso-burger-toc-hidden-color: #0e2431;
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

.with-toc #toc-area {
    grid-area: toc;
    height: 100vh;
    display: grid;
    grid-template-columns: auto;
    grid-template-rows: min-content 1fr;
    grid-template-areas:  "toggle" "tocnav";

}

.with-toc #top-menu {
    grid-area: toggle;
}

.with-toc #toc {
    overflow-y: auto;
    grid-area: tocnav;
}

.with-toc > header {
    grid-area: header;
}

.with-toc > main {
    grid-area: text;
    overflow-y: auto;
}

.with-toc > #top-menu {
    grid-area: burger
}

/******** Table of Contents ********/

#toc-area {
    background-color: var(--verso-toc-background-color);
    color: var(--verso-toc-text-color);
    width: 0em;
    transition: var(--verso-toc-transition-time);
}

#toc-area > * {
  width: 15em;
}

#toc-area:has(#toggle-toc:checked) {
    width: 15em;
}

#toc {
    transition: transform var(--verso-toc-transition-time), width 0.1s linear var(--verso-toc-transition-time);
    transform: translateX(-20em);
}

#toc-area:has(#toggle-toc:checked) #toc {
    transform: translateX(0);
}


#toggle-toc {
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

/*
header #print > *, header #controls > * {
    height: 3em;
    width: 3em;
    line-height: 3em;
    display: inline-block;
    text-align: center;
    vertical-align: center;
}
*/

#toggle-toc-click {
    cursor: pointer;
    /* This is the default, but it's needed to make the math work out so nice to be explicit: */
    box-sizing: content-box;
    width: var(--verso-burger-height);
    height: var(--verso-burger-height);
    display: flex;
    flex-direction: column;
    justify-content: space-between;
    padding: 0.5em;
}

#toggle-toc-click .line {
    display: block;
    height: var(--verso-burger-line-width);
    width: 100%;
    border-radius: var(--verso-burger-line-radius);
    background-color: var(--verso-burger-toc-hidden-color);
    /* The background color has a transition in case a theme needs to override the line color
       when the ToC menu is open */
    transition: background-color var(--verso-toc-transition-time) ease-in-out, transform var(--verso-toc-transition-time) ease-in-out;
}

#toc-area:has(#toggle-toc:checked) #toggle-toc-click .line {
    background-color: var(--verso-burger-toc-visible-color);
}

#toc-area:has(#toggle-toc:checked) #toggle-toc-click .line1 {
    transform:
        translateY(calc(calc(var(--verso-burger-height) - var(--verso-burger-line-width)) / 2))
        rotate(45deg);
}
#toc-area:has(#toggle-toc:checked) #toggle-toc-click .line2 {
    transform: scaleX(0);
}
#toc-area:has(#toggle-toc:checked) #toggle-toc-click .line3 {
    transform:
        translateY(calc(-1 * calc(calc(var(--verso-burger-height) - var(--verso-burger-line-width)) / 2)))
        rotate(-45deg);
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
