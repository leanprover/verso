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
    --verso-content-max-width: 45rem;

    /** Table of Contents appearance **/
    --verso-toc-background-color: #fafafa;
    --verso-toc-text-color: black;

    /* How long should the ToC animation take? */
    --verso-toc-transition-time: 0.4s;

    /* How wide should the ToC be on non-mobile? */
    --verso-toc-width: 15rem;

    /** Variables that control the “burger menu” appearance **/
    --verso-burger-height: 1.25rem;
    --verso-burger-width: 1.25rem;
    --verso-burger-line-width: 0.2rem;
    --verso-burger-line-radius: 0.2rem;
    --verso-burger-toc-visible-color: var(--verso-toc-text-color);
    --verso-burger-toc-visible-shadow-color: #ffffff;
    --verso-burger-toc-hidden-color: #0e2431;
    --verso-burger-toc-hidden-shadow-color: #ffffff;

    /* The "burger menu" may need to get bigger for mobile screens */
    --verso-mobile-burger-height: 2rem;
    --verso-mobile-burger-width: 2rem;
    --verso-mobile-burger-line-width: 0.4rem;
    --verso-mobile-burger-line-radius: 0.4rem;

}

/******** Global parameters not intended for customization by themes ********/

:root {
    /* How much space to add on the sides of content for small screens and to place widgets. */
    --verso--content-padding-x: 1.5rem;

}

/******** Reset ********/

body {
    margin: 0;
    padding: 0;
}

/******** Theme ********/

h1, h2, h3, h4, h5, h6 {
    font-family: var(--verso-structure-font-family);
    font-weight: bold;
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
    overflow-x: auto;
}

/******** Page Layout ********/

.with-toc #toc {
    position: fixed;
    z-index: 10;
}

/** Non-mobile **/
@media screen and (min-width: 701px) {
    .with-toc > main {
        /* NB main > section also has padding that's added to this in practice */
        padding-left: var(--verso-toc-width);
    }
}

/** Mobile **/
@media screen and (max-width: 700px) {
    .with-toc > main {
        padding-left: 1.5rem;
    }
}

.with-toc #toc {
    overflow-y: auto;
}

/******** Table of Contents ********/

#toc {
    background-color: var(--verso-toc-background-color);
    color: var(--verso-toc-text-color);
    display: flex;
    flex-direction: column;
    justify-content: space-between;
    height: 100dvh;
    width: var(--verso-toc-width);
}


#toc {
    /* Here, the width transition is delayed until after the translation has pushed
       the ToC off the screen. */
    transition: transform var(--verso-toc-transition-time) ease, width 0.1s linear var(--verso-toc-transition-time);
    transform: translateX(-20rem);
}

#toc:has(#toggle-toc:checked) {
    /* Here, the width transition must happen first, before the translation animation,
       so the translation is delayed.
     */
    transition: transform var(--verso-toc-transition-time) ease 0.1s, width 0.1s linear;
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
    padding-left: 0;
    padding-right: 0.5rem;
    margin-top: 1.5rem;
}

#toc .split-toc.book {
    margin-bottom: 2rem;
}

#toc .split-toc.book .title {
    font-weight: 600;
}

#toc .split-toc {
    margin-bottom: 1.5rem;
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
    --verso-toc-triangle-width: 0.6rem;
    --verso-toc-triangle-height: 0.6rem;
    --verso-toc-triangle-left-space: 0.5rem;
    --verso-toc-triangle-margin: 0.5rem;
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
    padding-left: 1.2rem;
    padding-top: 0.2rem;
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
  padding-bottom: 0.5rem;
}

#local-buttons {
    margin-top: 2.5rem;
    font-weight: bold;
    font-family: var(--verso-structure-font-family);
    display: flex;
    justify-content: space-between;
    margin-left: 0.5rem;
    margin-right: 0.5rem
}

#local-buttons > * {
    width: 4.5rem;
    display: flex;
    justify-content: center;
    align-items: center;
}

#local-buttons .local-button .where {
    margin: 0 0.3rem;
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
  max-width: min(80%, calc(100% - calc(var(--verso-burger-width) + 1rem)));
  max-height: 4rem;
  display: block;
  margin-left: auto;
  margin-right: 0.5rem;
  transition: height var(--verso-toc-transition-time) ease-in-out;
}

/******** Headerline ********/

header {
    display: grid;
    grid-template-columns: 1fr auto 1fr;
    grid-template-areas: "controls pagetitle print";
    align-items: center;
}

header h1 {
    margin-top: 0.2rem;
    margin-bottom: 0.2rem;
    text-align: center;
    grid-area: pagetitle;
    font-size: 1.25rem;
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

#toggle-toc-click {
    cursor: pointer;
    /* This is the default, but it's needed to make the math work out so nice to be explicit: */
    box-sizing: content-box;
    width: var(--verso-burger-width);
    height: var(--verso-burger-height);
    display: inline-flex;
    flex-direction: column;
    justify-content: space-between;
    padding: 0.5rem;
    position: fixed;
    z-index: 100; /* Show on top of ToC/content */
    filter: drop-shadow(1px 1px var(--verso-burger-toc-hidden-shadow-color)) drop-shadow(-1px -1px var(--verso-burger-toc-hidden-shadow-color));
    transition:
        height var(--verso-toc-transition-time) ease-in-out,
        width var(--verso-toc-transition-time) ease-in-out;
}

body:has(#toggle-toc:checked) #toggle-toc-click {
    filter: drop-shadow(1px 1px var(--verso-burger-toc-visible-shadow-color)) drop-shadow(-1px -1px var(--verso-burger-toc-visible-shadow-color));
}

@media screen and (max-width: 700px) {
    body {
        --verso-burger-width: var(--verso-mobile-burger-width);
        --verso-burger-height: var(--verso-mobile-burger-height);
        --verso-burger-line-width: var(--verso-mobile-burger-line-width);
        --verso-burger-line-radius: var(--verso-mobile-burger-line-radius);
    }
}

#toggle-toc-click .line {
    display: block;
    position: relative;
    width: 100%;
    height: var(--verso-burger-line-width);
    border-radius: var(--verso-burger-line-radius);
    background-color: var(--verso-burger-toc-hidden-color);
    /* The background color has a transition in case a theme needs to override the line color
       when the ToC menu is open */
    transition:
        background-color var(--verso-toc-transition-time) ease-in-out,
        height var(--verso-toc-transition-time) ease-in-out,
        width var(--verso-toc-transition-time) ease-in-out,
        transform var(--verso-toc-transition-time) ease-in-out;
    z-index: 15;
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
    padding: 0 1rem;
}
#meta-links li {
    display: inline-block;
}

/******** Text ********/

/*
For words that are too long to fit on the screen, it's better to wrap than to have horizontal scrolling
*/
main h1, main h2, main h3, main h4, main h5, main h6 {
  word-break: break-word;
}

main h1 {
  font-size: 2rem;
  line-height: 1.5;
  margin-bottom: 1.25rem;
}

main h2 {
  font-size: 1.6rem;
  line-height: 1.5;
  margin-bottom: 1rem;
}

main h3 {
  font-size: 1.4rem;
  line-height: 1.5;
  margin-bottom: 0.2rem;
}

main h4 {
  font-size: 1.2rem;
  line-height: 1.25;
  margin-bottom: 0.2rem;
}

main h5 {
  font-size: 1rem;
  line-height: 1.25;
  margin-bottom: 0.2rem;
}

main h6 {
  font-size: 1rem;
  line-height: 1.15;
  margin-bottom: 0rem;
}

main .titlepage h1 {
    text-align: center;
}

main .authors {
    text-align: center;
}

main > section {
    position: relative;
    padding: var(--verso--content-padding-x);
}

main section {
    max-width: var(--verso-content-max-width);
}

main ol.section-toc, main .section-toc ol {
    list-style-type: none;
}

main ol.section-toc {
    /* This is to "undo" the text-indent: -3rem on the LI elements, which indents
       subsequent lines but not the section number. */
    padding-left: 3rem;
}

main .section-toc > li {
    padding-bottom: 0.25rem;
}

main .section-toc ol {
    padding-left: 0.5rem
}

main .section-toc li {
    font-weight: bold;
    font-family: var(--verso-structure-font-family);
    margin-left: 1rem;
    /* Indent text that isn't a section number */
    text-indent: -3rem;
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
    opacity: 0;
    text-decoration: none;
    font-size: 50%;
    vertical-align: 10%;
    margin-left: 0.5rem;
    width: 0;
    position: relative;
}

.permalink-widget.inline > a {
    position: absolute;
    bottom: 0;
    left: 0;
}

:hover > .permalink-widget.inline {
    opacity: 1;
}


:has(> .permalink-widget.block) {
    position: relative;
}

:hover > .permalink-widget.block {
    opacity: 1;
}

.permalink-widget.block {
    position: absolute;
    right: calc(-1 * var(--verso--content-padding-x));
    top: 0;
    opacity: 0.1;
    transition: opacity 0.5s;
}

/* On narrow screens, float the widget over the block instead of
   putting it in the margin to avoid horizontal scrolling. */
@media screen and (max-width: 700px) {
    .permalink-widget.block {
        right: 0;
        opacity: 1;
    }
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
