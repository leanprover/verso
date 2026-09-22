/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Verso
public import Verso.Doc.ArgParse
public import Verso.Doc.Elab.Monad
public import Verso.Code
public import VersoManual.Basic
public import VersoManual.Html.Hoist
public meta import Verso.Doc.Elab.Inline
meta import Verso.Doc.Elab.InlineString
meta import MultiVerso.Slug

public section

namespace Verso.Genre.Manual

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open Verso.Genre.Manual.Html
open SubVerso.Highlighting Highlighted

def Marginalia.css := r#"
.marginalia-note {
  box-sizing: border-box;
  padding: 0.5rem;
  font-family: var(--verso-text-font-family);
  font-size: 1rem;
  font-weight: normal;
  font-style: normal;
  line-height: 1.45;
  color: var(--verso-text-color);
  text-align: left;
  white-space: normal;
}

/* Neutralize the user-agent popover box when the note is participating in document layout.
   The user agent makes popovers scroll containers, which would clip the number that ::before
   places to the left of the note. */
.marginalia-note[popover] {
  border: 0;
  background: transparent;
  color: inherit;
  box-shadow: none;
  overflow: visible;
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
  .marginalia-note[popover] {
    position: static;
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
  .marginalia-note[popover] {
    display: block;
    position: relative;
    inset: auto;
    float: right;
    clear: right;
    width: 40%;
    margin: 1rem 0;
    margin-left: 10%;
  }

  /* The first note moved immediately before a barrier starts at the barrier's position. */
  .marginalia-note[data-verso-hoisted="before"]:not(.marginalia-note + .marginalia-note) {
    margin-top: 0;
  }
}

/* Left-aligned content: a fixed-size note in the wide area to its right. */
@container main (width >= 1112px) {
  .marginalia-note[popover] {
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
  .marginalia-note[popover] {
    width: 15cqi;
    margin-right: -18cqi;
  }
}

.marginalia-reference.marginalia-highlight, .marginalia-note.marginalia-highlight {
  background-color: var(--verso-selected-color, #def);
  border-radius: 0.2rem;
}

/* The counter must be established inside <main>, whose container declaration (see
   Html/Style.lean) applies style containment: a counter established outside the
   containment boundary cannot be incremented by the notes within it. */
.content-wrapper {
  counter-reset: margin-note-reference-counter margin-note-body-counter;
}

.content-wrapper::after {
  content: "";
  display: block;
  clear: both;
  height: 1rem;
}

.marginalia-reference {
  counter-increment: margin-note-reference-counter;
}
.marginalia-note {
  counter-increment: margin-note-body-counter;
}
.marginalia-note::before {
  content: counter(margin-note-body-counter) ".";
  position: absolute;
  vertical-align: baseline;
  font-size: 0.9em;
  font-weight: bold;
  left: -3rem;
  width: 3rem;
  text-align: right;
}
.marginalia-marker::after {
  content: counter(margin-note-reference-counter);
  vertical-align: super;
  font-size: 0.7em;
  font-weight: bold;
  margin-right: 0.5em;
}

.marginalia-marker-mobile {
  display: none;
}

.marginalia-accessible-label {
  position: absolute;
  width: 1px;
  height: 1px;
  padding: 0;
  margin: -1px;
  overflow: hidden;
  clip: rect(0, 0, 0, 0);
  white-space: nowrap;
  border: 0;
}

@supports selector(:popover-open) {
  @media screen and (width <= 700px) {
    .marginalia-marker-desktop {
      display: none;
    }

    .marginalia-marker-mobile {
      display: inline;
      appearance: none;
      border: 0;
      padding: 0;
      color: inherit;
      background: transparent;
      font: inherit;
      cursor: pointer;
    }

    .marginalia-marker-mobile:focus-visible {
      outline: 2px solid currentColor;
      outline-offset: 2px;
    }

    .marginalia-note[popover] {
      position: fixed;
      float: none;
      inset: 50% auto auto 50%;
      width: calc(100vw - 2rem);
      max-width: min(32rem, calc(100vw - 2rem));
      max-height: calc(100vh - 2rem);
      margin: 0;
      transform: translate(-50%, -50%);
      overflow: auto;
      border: 1px solid currentColor;
      background: var(--verso-code-background-color, white);
      color: inherit;
      box-shadow: 0 0.5rem 2rem rgb(0 0 0 / 30%);
    }

    .marginalia-note[popover]::before {
      content: none;
    }

    .marginalia-note[popover]::backdrop {
      background: rgb(0 0 0 / 18%);
    }
  }
}
"#

def Marginalia.js := r#"
(() => {
  const setupHover = () => {
    document.querySelectorAll(".marginalia-reference").forEach(reference => {
      const marker = reference.querySelector("[aria-details]");
      const note = marker && document.getElementById(marker.getAttribute("aria-details"));
      if (!note) return;

      const highlight = () => {
        reference.classList.add("marginalia-highlight");
        note.classList.add("marginalia-highlight");
      };
      const unhighlight = () => {
        reference.classList.remove("marginalia-highlight");
        note.classList.remove("marginalia-highlight");
      };
      reference.addEventListener("pointerenter", highlight);
      reference.addEventListener("pointerleave", unhighlight);
      note.addEventListener("pointerenter", highlight);
      note.addEventListener("pointerleave", unhighlight);
    });
  };

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", setupHover, {once: true});
  } else {
    setupHover();
  }

  const mobile = matchMedia("(width <= 700px)");
  mobile.addEventListener("change", event => {
    if (!event.matches) {
      document.querySelectorAll(".marginalia-note:popover-open")
        .forEach(note => note.hidePopover());
    }
  });
})();
"#

open Verso.Output Html in
/--
Renders marginal content with desktop and mobile markers that refer to the note by {name}`id`, which
must be unique.

The note is hoistable up to {lean}`"margin"` barriers, and its markers are removed when marginal
content is suppressed.
-/
def Marginalia.html (content : Html) (id : String) : Html :=
  let reference := Hoist.suppressible "margin" {{
    <span class="marginalia-reference">
      <span class="marginalia-marker marginalia-marker-desktop" aria-details={{id}}>
        <span class="marginalia-accessible-label">"Marginal note"</span>
      </span>
      <button class="marginalia-marker marginalia-marker-mobile"
              type="button"
              aria-details={{id}}
              "popovertarget"={{id}}>
        <span class="marginalia-accessible-label">"Show marginal note"</span>
      </button>
    </span>
  }}
  let note := Hoist.hoist "margin" {{
    <span class="marginalia-note" id={{id}} role="note" "popover"="auto">{{content}}</span>
  }}
  reference ++ note

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

inline_extension Inline.margin (idSlug : String) where
  data := ToJson.toJson idSlug
  traverse id data _ := do
    let path ← (·.path) <$> read
    let hint := s!"--marginalia-{(FromJson.fromJson? data (α := String)).toOption.getD ""}"
    let _ ← Verso.Genre.Manual.externalTag id path hint
    pure none
  toTeX :=
  open Verso.Output.TeX in
  some <| fun goI _ _ content => do
    pure <| Marginalia.TeX (← content.mapM goI)
  extraCss := [Marginalia.css]
  extraJs := [Marginalia.js]
  toHtml :=
    open Verso.Output.Html Doc.Html.HtmlT in
    some <| fun goI id inl content  => do
      let some link := (← state).externalTags[id]?
        | panic! s!"Untagged marginalia with data {inl}"
      pure <| Marginalia.html (← content.mapM goI) link.htmlId.toString

namespace Marginalia
open Verso.Multi

/-- The number of characters from a note's text to use in its HTML `id` attribute. -/
meta def idSlugLength : Nat := 32

/--
Computes the text that seeds a margin note's HTML id from its plain-text preview: the sluggified
text, truncated to {name}`idSlugLength` characters, so that ids on a page with many notes stay
short and distinct.
-/
meta def idSlug (preview : String) : String :=
  preview.sluggify.toString.take idSlugLength |>.copy

end Marginalia

open Marginalia in
@[role]
meta def margin : RoleExpanderOf Unit
  | (), inlines => do
    let slug := idSlug <| inlineToString (← getEnv) <| mkNullNode inlines
    let content ← inlines.mapM elabInline
    ``(Doc.Inline.other (Inline.margin $(quote slug)) #[$content,*])

open Lean.Doc.Syntax in
/--
Margin notes should be dropped from plain-text previews.
-/
@[inline_to_string Lean.Doc.Syntax.role]
meta def margin.inline_to_string : InlineToString
  | _, `(inline| role{ $name $_* }[ $_* ]) =>
    if name.getId ∈ [`margin, ``margin] then some "" else none
  | _, _ => none
