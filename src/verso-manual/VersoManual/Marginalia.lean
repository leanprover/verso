/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import Verso.Code
import VersoManual.Basic

namespace Verso.Genre.Manual

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

def Marginalia.css := r#"
.marginalia .note {
  position: relative;
  padding: 0.5rem;
}

/*
The margin-note layout responds to the width of <main>, not the viewport, because the
ToC is resizable: a wider ToC leaves less room beside the text for notes. <main> is a
query container (see Html/Style.lean), so the container queries below track the actual
content width.

There are two "in the margin" regimes, split at the same width where the content stops
being left-aligned and becomes centered (1112px and 1212px of content width; at the
default ToC width these are the old 1400px and 1500px viewport breakpoints):

  * While the content is left-aligned there is a large area to its right, so a fixed
    13rem note with a fixed 16rem overhang fits comfortably.
  * Once the content is centered the note must fit the symmetric right gap, whose width
    is (content - text column) / 2. A fixed overhang would overflow the page for content
    widths just above the centering threshold, so the note and its overhang are sized in
    container units, which always fit that gap.
*/

/* Narrow viewport (e.g. phone): the ToC is hidden and the note spans the text column. */
@media screen and (width <= 700px) {
  .marginalia .note {
    float: left;
    clear: left;
    width: 90%;
    margin: 1rem 5%;
  }
}

/* Wider than a phone: by default float the note at the right of the text column,
   overlapping the content. The container queries below lift it into the true margin
   once there is room. */
@media screen and (min-width: 701px) {
  .marginalia .note {
    float: right;
    clear: right;
    width: 40%;
    margin: 1rem 0;
    margin-left: 10%;
  }
}

/* Left-aligned content: a fixed-size note in the wide area to its right. */
@container main (width >= 1112px) {
  .marginalia .note {
    float: right;
    clear: right;
    width: 13rem;
    margin: 1rem -16rem 0 0;
  }
}

/* Centered content: size the note in container units so it always fits the symmetric
   right gap. The threshold matches the content-centering threshold in Html/Style.lean,
   so the fixed-overhang note above is only ever used while the content is left-aligned.
   The overhang (18cqi) stays below the gap, (100cqi - text column) / 2, for every
   content width at which the content is centered. */
@container main (width >= 1212px) {
  .marginalia .note {
    width: 15cqi;
    margin-right: -18cqi;
  }
}

.marginalia:hover, .marginalia:hover .note, .marginalia:has(.note:hover) {
  background-color: var(--lean-accent-light-blue);
}

body {
  counter-reset: margin-note-counter;
}
.marginalia .note {
  counter-increment: margin-note-counter;
}
.marginalia .note::before {
  content: counter(margin-note-counter) ".";
  position: absolute;
  vertical-align: baseline;
  font-size: 0.9em;
  font-weight: bold;
  left: -3rem;
  width: 3rem;
  text-align: right;
}
.marginalia::after {
  content: counter(margin-note-counter);
  vertical-align: super;
  font-size: 0.7em;
  font-weight: bold;
  margin-right: 0.5em;
}
"#

open Verso.Output Html in
def Marginalia.html (content : Html) : Html :=
  {{<span class="marginalia"><span class="note">{{content}}</span></span>}}

/-
This is a slight misnomer as it is not literally rendered as a margin
note, but rather a footnote. Nonetheless this code is here as it is
the TeX/PDF analogue of the marginal notes that we render in HTML for
bibliographic citations, and probably if there are other things that
we wish to render as marginal notes in HTML, arguably it makes more
stylistic sense to render them as footnotes in a fundamentally
paginated format.
-/
open Verso.Output TeX in
def Marginalia.TeX (content : TeX) : TeX :=
  \TeX{ \footnote{ \Lean{ content } } }

inline_extension Inline.margin where
  traverse _ _ _ := do
    pure none
  toTeX :=
  open Verso.Output.TeX in
  some <| fun goI _ _ content => do
    pure <| Marginalia.TeX (← content.mapM goI)
  extraCss := [Marginalia.css]
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI _ _ content  => do
      Marginalia.html <$> content.mapM goI

@[role]
def margin : RoleExpanderOf Unit
  | (), inlines => do
    let content ← inlines.mapM elabInline
    ``(Doc.Inline.other Inline.margin #[$content,*])
