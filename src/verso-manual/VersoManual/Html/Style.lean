/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

namespace Verso.Genre.Manual.Html.Css

def pageStyle : String := r####"
/******** Customizability ********/

:root {
    /** Typography **/
    /* What's the maximum line width, for legibility? */
    --verso-content-max-width: 47rem;
    /* Desktop font size */
    --verso-font-size: 16px;
    /* Mobile font size */
    --verso-mobile-font-size: 16px;

    /** Header appearance **/
    --verso-header-height: 3rem;
    /* Height of the displayed logo **/
    --verso-logo-height: var(--verso-header-height);

    /** Table of Contents appearance **/
    --verso-toc-background-color: #fafafa;
    --verso-toc-text-color: var(--verso-text-color);

    /* How long should the ToC animation take? */
    --verso-toc-transition-time: 0.4s;

    /* How wide should the ToC be on non-mobile? */
    --verso-toc-width: 18rem;

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
    --verso-mobile-burger-height: 1.5rem;
    --verso-mobile-burger-width: 1.5rem;
    --verso-mobile-burger-line-width: 0.3rem;
    --verso-mobile-burger-line-radius: 0.3rem;
}

/******** Global parameters not intended for customization by themes ********/

:root {
    /* How much space to add on the sides of content for small screens and to place widgets. */
    --verso--content-padding-x: 1.5rem;

    /* Vertical margin for definition boxes and examples */
    --verso--box-vertical-margin: 1.5rem;
    --verso--box-padding: 1rem;
}

@media screen and (max-width: 700px) {
  :root {
    /* Reduce the standard padding on mobile */
    --verso--content-padding-x: 1rem;
  }
}

/******** Root font size - this is what rem is based on *********/

html {
    font-size: var(--verso-font-size);
}

@media screen and (max-width: 700px) {
    html {
        font-size: var(--verso-mobile-font-size);
    }
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
    line-height: 1.45;
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
    overflow-y: clip;
}

/******** Page Layout ********/

header {
	position: fixed;
	top: 0;
	z-index: 99;
	left: 0;
	right: 0;
	background: white;
	display: flex;
	align-items: center;
	height: var(--verso-header-height);
	box-shadow: 0 0px 6px lightgray;
}

.header-logo-wrapper {
    /* Make the logo always take up the same space as the toc */
    flex-basis: var(--verso-toc-width);
    /* Make padding be included in the width calculation */
    box-sizing: border-box;
    /* Add padding so it doesn't sit at the very edge of the screen. */
    padding-left: .5rem;
}

@media screen and (max-width: 700px) {
    .header-logo-wrapper {
        display: none;
    }
}

.header-title-wrapper {
    /* The title wrapper grows to fill up the header */
    flex: 1;
}

@media screen and (max-width: 1500px) {
    /* Add the padding of the content when the content moves to the left */
    padding-left: var(--verso--content-padding-x);
}

.header-title {
    text-decoration: none;
    color: black;
    font-size: 2rem;
    font-weight: bold;
    display: block;
    margin: 0 auto;
    max-width: var(--verso-content-max-width);
}

@media screen and (max-width: 1500px) {
    /* Move the title to the left, to align with the content that does the same. */
    .header-title {
        margin: 0;
        max-width: unset;
    }
}

@media screen and (max-width: 700px) {
    /* There's no header logo on mobile, so the title just needs to reserve space for the burger */
    .header-title {
        margin-left: calc(var(--verso-burger-width) + 1.5rem); /* There's 0.5 rem padding on the burger, and we want some space */
        max-width: unset;
    }
}

.header-title h1 {
    margin: 0;
    font-size: inherit;
    font-weight: inherit;
    text-wrap: nowrap;
}

:root:has(header:empty) {
    --verso-header-height: 0px;
}

.with-toc {
    margin-top: var(--verso-header-height);
}

main [id] {
  /* When jumping to something, display it below the header. We also add a little
     whitespace, so it's easier to see that you are indeed viewing the whole item. */
  scroll-margin-top: calc(var(--verso-header-height) + 1rem);
}

.with-toc #toc {
    position: fixed;
    z-index: 10;
}

/** Non-mobile **/
.with-toc > main {
    /* NB main > section also has padding that's added to this in practice */
    padding-left: var(--verso-toc-width);
}

/** Mobile **/
@media screen and (max-width: 700px) {
    .with-toc > main {
        padding-left: 0;
    }
}

.with-toc #toc {
    overflow-y: auto;
}


/******** Table of Contents ********/

/* This backdrop should be hidden on desktop browsers, and show up when the ToC is open on mobile browsers */
.toc-backdrop {
    display: none;
}

@media screen and (max-width: 700px) {
    .toc-backdrop {
        display: block;
    }
    body:has(#toggle-toc:checked) .toc-backdrop {
        position: fixed;
        inset: 0;
        background-color: #aaa8;
        z-index: 9;
    }
    html:has(#toggle-toc:checked) {
        overflow: hidden;
    }
}

#toc {
    background-color: var(--verso-toc-background-color);
    color: var(--verso-toc-text-color);
    display: flex;
    flex-direction: column;
    justify-content: space-between;
    height: calc(100dvh - var(--verso-header-height));
    width: var(--verso-toc-width);
}

@media screen and (max-width: 700px) {
    #toc {
        /* Push the toc off the page on mobile */
        right: 100%;
        transition: transform var(--verso-toc-transition-time) ease;
    }

    #toc:has(#toggle-toc:checked) {
        transform: translateX(var(--verso-toc-width));
    }
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

.toc-title {
    /* The ToC title can be displayed when there is no room for the title in the header. */
    display: none;
    padding: 0 .5rem;
}

.toc-title h1 {
    margin-bottom: 0;
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
}

#toc .split-toc > ol {
    border-left: 1px dotted;
    list-style-type: none;
    padding-left: 0.5rem;
    margin-left: 0;
    margin-right: 0;
    margin-bottom: 0.5rem;
    margin-top: 0.5rem;
    font-size: 0.9rem;
}

#toc .split-toc > ol > li {
    text-indent: -1.5rem;
    padding-left: 2.5rem;
}

#toc .split-toc > ol > li:has(.header) {
    padding-left: 2rem;
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

.prev-next-buttons {
    font-weight: bold;
    font-family: var(--verso-structure-font-family);
    display: flex;
    justify-content: space-between;
    flex-wrap: wrap;
    max-width: var(--verso-content-max-width);
}

.prev-next-buttons > * {
    display: flex;
    flex: 1;
    justify-content: center;
    align-items: center;
    color: black;
    text-decoration: none;
}

.prev-next-buttons > [rel=prev] {
    justify-content: start;
}

.prev-next-buttons > [rel=next] {
    justify-content: end;
}

.prev-next-buttons .local-button .where {
    margin: 0 0.3rem;
    /* Fix the position relative to the arrows. */
    position: relative;
    top: 0.1rem;
}

.prev-next-buttons .arrow {
    font-family: var(--verso-code-font-family);
    font-size: 150%;
}

#logo {
    max-height: 100%;
    display: block;
}

#logo img {
    object-fit: contain;
    max-height: var(--verso-logo-height);
    display: block;
}

/******** Width-dependent layout elements ********/

.narrow-only {
    display: none;
}

@media screen and (max-width: 500px) {
    .wide-only {
        display: none;
    }
    .narrow-only {
        display: revert;
    }
}

@media screen and (min-width: 700px) and (max-width: 920px){
    .wide-only {
        display: none;
    }
    .narrow-only {
        display: revert;
    }
}


/******** Headerline ********/

#toggle-toc-click {
    /* Hidden on desktop */
    display: none;
}

@media screen and (max-width: 700px) {
    #toggle-toc-click {
        display: inline-flex;
        cursor: pointer;
        /* This is the default, but it's needed to make the math work out so nice to be explicit: */
        box-sizing: content-box;
        width: var(--verso-burger-width);
        height: var(--verso-burger-height);
        flex-direction: column;
        justify-content: space-between;
        padding: 0.5rem;
        position: fixed;
        z-index: 100; /* Show on top of ToC/content */
        /* Calculation to make it sit in the middle of the header. The .5rem is the padding added to #toggle-toc-click. */
        top: calc((var(--verso-header-height) - var(--verso-burger-height) - 2 * .5rem) / 2);
        filter: drop-shadow(1px 1px var(--verso-burger-toc-hidden-shadow-color)) drop-shadow(-1px -1px var(--verso-burger-toc-hidden-shadow-color));
        transition:
            height var(--verso-toc-transition-time) ease-in-out,
            width var(--verso-toc-transition-time) ease-in-out;
    }

    body:has(#toggle-toc:checked) #toggle-toc-click {
        filter: drop-shadow(1px 1px var(--verso-burger-toc-visible-shadow-color)) drop-shadow(-1px -1px var(--verso-burger-toc-visible-shadow-color));
    }

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
  overflow-wrap: break-word;
}

main h1 {
  font-size: 2.3rem;
  line-height: 1.5;
  margin-bottom: 1.3rem;
}

main h2 {
  font-size: 1.7rem;
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
  font-weight: 500;
  line-height: 1.15;
  margin-bottom: 0rem;
}

main .titlepage h1 {
    text-align: center;
}

main .authors {
    text-align: center;
    font-family: var(--verso-structure-font-family);
}

main .authors {
    text-align: center;
    font-family: var(--verso-structure-font-family);
}

main .authors .author:only-of-type::after {
    content: "";
}

main .authors .author:not(:last-of-type)::after {
    content: ", ";
}

main .authors .author:nth-last-of-type(2)::after {
    content: " and ";
}

main .authors .note {
    margin: 0;
    display: inline;
    font-style: italic;

}
main .authors:has(.author) .note::before {
  content: ", ";
}

/******** Main content ********/

.content-wrapper {
    padding: var(--verso--content-padding-x);
    max-width: var(--verso-content-max-width);
    margin: 0 auto;
}

@media screen and (max-width: 1500px) {
    /* Left align the content when less than 1500px, to make room for the footnotes on the right. */
    .content-wrapper {
        margin: 0;
        max-width: unset;
    }
}

main > section {
    position: relative;
}

@media screen and (max-width: 700px) {
    /* Remove extra margin on mobile. */
    main > section > :first-child {
        margin-top: 0;
    }
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

/******** Manual-specific changes to highlighted Lean code ********/

/* Don't scroll horizontally due to long identifiers (e.g. option names) */
@media screen and (max-width: 700px) {
    .hl.lean.inline {
        overflow-wrap: break-word;
    }
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

/*
Don't shrink code blocks when there's marginalia that overlaps
*/
@media screen and (700px < width <= 1400px) {
  .hl.lean.block {
    clear: right;
  }
}

/*
Don't shrink doc blocks when there's marginalia that overlaps
*/
@media screen and (700px < width <= 1400px) {
  .namedocs {
    clear: right;
  }
}


section > p, section > ul, section > ol {
    margin-top: 1rem;
    margin-bottom: 1rem;
}

div.paragraph > p:not(:first-child),
div.paragraph > ul:not(:first-child),
div.paragraph > ol:not(:first-child),
div.paragraph > code.hl.lean.block:not(:first-child),
div.paragraph > pre.syntax-error:not(:first-child),
div.paragraph > dl:not(:first-child) {
  margin-top: 0.5rem;
}

div.paragraph > p:not(:last-child),
div.paragraph > ul:not(:last-child),
div.paragraph > ol:not(:last-child),
div.paragraph > code.hl.lean.block:not(:last-child),
div.paragraph > pre.syntax-error:not(:last-child),
div.paragraph > dl:not(:last-child) {
  margin-bottom: 0.5rem;
}

ol li::marker {
  font-family: var(--verso-text-font-family);
}

/*
Don't impose margins on lists or list items from their contents.
*/
main section li > :first-child {
  margin-top: 0;
}
main section li > :last-child {
  margin-bottom: 0;
}
main section li:not(:first-child) {
  margin-top: 0.5rem;
}
main section li:not(:last-child) {
  margin-bottom: 0.5rem;
}
main section li ol {
  margin-top: .5rem;
}

.hl.lean.block {
    margin-top: 1em;
    margin-bottom: 1em;
    margin-left: 0.75em;
}

.lean-output {
    overflow-x: auto;
    margin: 0px;
    margin: 0.5em .85em;
    border-left: 0.2em solid red;
    padding: 0 0.45em;
}

/* Different color for warning */
.lean-output.warning {
    border-color: var(--verso-warning-color);
}

/* Different color for information */
.lean-output.information {
    border-color: #0000c0;
}


/* TODO: fix upstream */
.hl.lean code {
    font-family: var(--verso-code-font-family) !important;
}

"####
