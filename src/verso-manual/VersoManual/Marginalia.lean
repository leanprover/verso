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

/* Wide viewport */
@media screen and (min-width: 1400px) {
  .marginalia .note {
    float: right;
    clear: right;
    margin-right: -16rem;
    width: 13rem;
    margin-top: 1rem;
  }
}

/* Very wide viewport */
@media screen and (min-width: 1600px) {
  .marginalia .note {
    margin-right: -19vw;
    width: 15vw;
  }
}

.marginalia:hover, .marginalia:hover .note, .marginalia:has(.note:hover) {
  background-color: var(--lean-accent-light-blue);
}

/* Medium viewport */
@media screen and (700px < width <= 1400px) {
  .marginalia .note {
    float: right;
    clear: right;
    width: 40%;
    margin: 1rem 0;
    margin-left: 10%;
  }
}

/* Narrow viewport (e.g. phone) */
@media screen and (width <= 700px) {
  .marginalia .note {
    float: left;
    clear: left;
    width: 90%;
    margin: 1rem 5%;
  }
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
