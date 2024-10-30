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
    grid-template-rows: auto;
    grid-template-areas:
        "toc text";
    height: 100vh;
    overflow: hidden;
}

.with-toc #toc {
    grid-area: toc;
    height: 100vh;
}

.with-toc #top-menu {
    grid-area: toggle;
}

.with-toc #toc {
    overflow-y: auto;
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

#toc {
    background-color: var(--verso-toc-background-color);
    color: var(--verso-toc-text-color);
    display: flex;
    flex-direction: column;
    justify-content: space-between;
}

#toc {
  width: 15em;
}


#toc {
    /* Here, the width transition is delayed until after the translation has pushed
       the ToC off the screen. */
    transition: transform var(--verso-toc-transition-time) ease, width 0.1s linear var(--verso-toc-transition-time);
    transform: translateX(-20em);
    width: 0;
}

#toc:has(#toggle-toc:checked) {
    /* Here, the width transition must happen first, before the translation animation,
       so the translation is delayed.
     */
    transition: transform var(--verso-toc-transition-time) ease 0.1s, width 0.1s linear;
    transform: translateX(0);
    width: 15em;
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
    padding-left: 0;
    padding-right: 0.5em;
    margin-top: 1.5em;
}

#toc .split-toc.book {
    margin-bottom: 2em;
}

#toc .split-toc.book .title {
    font-weight: 600;
}

#toc .split-toc {
    margin-bottom: 1.5em;
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

:root {
    --verso-toc-triangle-width: 0.6em;
    --verso-toc-triangle-height: 0.6em;
    --verso-toc-triangle-left-space: 0.5em;
    --verso-toc-triangle-margin: 0.5em;
}

#toc .split-toc label.toggle-split-toc::before {
    width: calc(var(--verso-toc-triangle-width) + var(--verso-toc-triangle-left-space));
    height: var(--verso-toc-triangle-height);
    display: inline-block;
    background-color: black;
    content: ' ';
    transition: ease 0.2s;
    margin-right: var(--verso-toc-triangle-margin);
    clip-path: polygon(100% 0, var(--verso-toc-triangle-left-space) 0, calc(var(--verso-toc-triangle-left-space) + calc(calc(100% - var(--verso-toc-triangle-left-space)) / 2)) 100%);
    transform-origin:
        /* X axis: left spacing plus half the width to get the center*/
        calc(var(--verso-toc-triangle-left-space) + calc(var(--verso-toc-triangle-width) / 2))
        /* Y axis */
        center;
}

#toc .split-toc label.toggle-split-toc:has(input[type="checkbox"]:not(:checked))::before {
    transform: rotate(-90deg);
}

#toc .split-toc .no-toggle {
    /* Line up triangle-less content with the triangled content */
    width: calc(var(--verso-toc-triangle-width) + var(--verso-toc-triangle-left-space));
    margin-right: var(--verso-toc-triangle-margin);
    display: inline-block;
}

#toc .split-toc > :not(:first-child) {
    max-height: 0px;
    display: block;
    overflow: hidden;
    /* Line it up with the point of the disclosure triangle */
    margin-left: calc(var(--verso-toc-triangle-left-space) + calc(var(--verso-toc-triangle-width) / 2));
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

#toc .split-toc td {
    vertical-align: top;
    font-size: 90%;
}

#toc .split-toc .current td:not(.num), #toc .split-toc .title .current {
    text-decoration-line: underline;
    text-decoration-style: dotted;
}

#toc .split-toc td.num {
    font-variant-numeric: tabular-nums;
}

/* Add a bit of visual space between numbered and unnumbered rows */
#toc .split-toc tr:has(+ tr.unnumbered) td, #toc .split-toc tr.unnumbered:has(+ tr.numbered) td {
  padding-bottom: 0.5em;
}

#local-buttons {
    margin-top: 2.5em;
    font-weight: bold;
    font-family: var(--verso-structure-font-family);
    display: flex;
    justify-content: space-between;
    margin-left: 0.5em;
    margin-right: 0.5em
}

#local-buttons > * {
    width: 4.5em;
    display: flex;
    justify-content: center;
    align-items: center;
}

#local-buttons .local-button .where {
    margin: 0 0.3em;
}

.local-button.active {
    color: var(--verso-toc-text-color);
    border: 1px solid var(--verso-toc-background-color);
}

.local-button.inactive {
    color: color-mix(in srgb, var(--verso-toc-text-color), var(--verso-toc-background-color));
    border: 1px solid var(--verso-toc-background-color);
    cursor: default;
}


#local-buttons a.local-button.active {
    text-decoration: none;
}

#local-buttons a.local-button.active:hover {
    text-decoration: none;
    background-color: color-mix(in srgb, white, var(--verso-toc-background-color));
    border-color: color-mix(in srgb, var(--verso-toc-text-color) 30%, var(--verso-toc-background-color) 70%);
}

#local-buttons .local-button.inactive:hover {

}


#local-buttons .arrow {
    font-family: var(--verso-code-font-family);
    font-size: 150%;
}

#logo {
  max-width: min(80%, calc(100% - calc(var(--verso-burger-width) + 1em)));
  max-height: 4em;
  display: block;
  margin-left: calc(var(--verso-burger-width) + 1em); /* Make space for the menu button */
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
    display: inline-flex;
    flex-direction: column;
    justify-content: space-between;
    padding: 0.5em;
    position: absolute;
    z-index: 100; /* Show on top of ToC/content */
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

body:has(#toggle-toc:checked) #toggle-toc-click .line {
    background-color: var(--verso-burger-toc-visible-color);
}

body:has(#toggle-toc:checked) #toggle-toc-click .line1 {
    transform:
        translateY(calc(calc(var(--verso-burger-height) - var(--verso-burger-line-width)) / 2))
        rotate(45deg);
}
body:has(#toggle-toc:checked) #toggle-toc-click .line2 {
    transform: scaleX(0);
}
body:has(#toggle-toc:checked) #toggle-toc-click .line3 {
    transform:
        translateY(calc(-1 * calc(calc(var(--verso-burger-height) - var(--verso-burger-line-width)) / 2)))
        rotate(-45deg);
}


#meta-links {
    list-style-type: none;
    font-family: var(--verso-structure-font-family);
    font-size: 90%;
    display: flex;
    justify-content: space-between;
    padding: 0 1em;
}
#meta-links li {
    display: inline-block;
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
    position: relative;
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

/******** Permalink widgets ********/

.permalink-widget.inline {
  display: none;
  text-decoration: none;
  font-size: 50%;
  vertical-align: 10%;
  margin-left: 0.5em;
}

:hover > .permalink-widget.inline {
  display: inline-block;
}


:has(> .permalink-widget.block) {
    position: relative;
}

:hover > .permalink-widget.block {
    opacity: 1;
}

.permalink-widget.block {
    position: absolute;
    right: -1.5em;
    top: 0;
    opacity: 0.1;
    transition: opacity 0.5s;
}

.permalink-widget > a {
  /* Don't show the colors here */
  color: transparent;
  text-shadow: 0 0 0 gray;
  text-decoration: none;
}

.permalink-widget > a:hover {
  text-decoration: none;
}

"####

def pageStyleJs : String := r####"
function saveCheckboxesInit() {
  for (checkbox of document.querySelectorAll('#toc input[type="checkbox"]')) {
    const value = localStorage.getItem(checkbox.id);
    if (value === "true") {
        checkbox.checked = true;
    } else if (value === "false") {
        checkbox.checked = false;
    } // if not found, do nothing
    checkbox.addEventListener("change", persistCheckbox);
  }
}

function persistCheckbox() {
  const value = this.checked; // in a handler, 'this' is the element with the handler on it
  const id = this.id;
  localStorage.setItem(this.id, value ? "true" : "false");
}

window.addEventListener("DOMContentLoaded", saveCheckboxesInit);
"####
