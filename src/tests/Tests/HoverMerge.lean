/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import all Verso.Code.Highlighted
meta import Verso.Output.Html
meta import SubVerso.Highlighting

open SubVerso.Highlighting (Highlighted)
open Verso.Code (takeAttr)
open Verso.Output (Html)

namespace Verso.HoverMergeTest

/-!
These helpers support merging a documented token's hover content into a message span that
shares the token's extent: `Highlighted.normalize` makes the sole-token shape recognizable,
and `takeAttr` moves the token's hover attributes up to the span.
-/

def tok : Html := .tag "span" #[("class", "token"), ("data-verso-hover", "5")] (.text true "x")
def tokNoHover : Html := .tag "span" #[("class", "token")] (.text true "x")

-- The attribute is taken from a bare element.
#guard takeAttr "data-verso-hover" tok == (some "5", tokNoHover)

-- The attribute is found through a wrapping element, such as a link.
#guard takeAttr "data-verso-hover" (.tag "a" #[("href", "x.html")] tok) ==
  (some "5", .tag "a" #[("href", "x.html")] tokNoHover)

-- Other attributes are found where they live, such as extra links on the wrapping element.
#guard takeAttr "data-verso-links" (.tag "a" #[("data-verso-links", "[]")] tok) ==
  (some "[]", .tag "a" #[] tok)

-- The outermost attribute wins, and inner ones are left in place.
#guard takeAttr "data-verso-hover" (.tag "a" #[("data-verso-hover", "9")] tok) ==
  (some "9", .tag "a" #[] tok)

-- Empty content around a sole element does not block the search.
#guard takeAttr "data-verso-hover" (.seq #[.text true "", tok, .seq #[]]) == (some "5", tokNoHover)

-- Adjacent content blocks the search, including whitespace.
#guard takeAttr "data-verso-hover" (.seq #[tok, .text true "y"]) == (none, .seq #[tok, .text true "y"])
#guard takeAttr "data-verso-hover" (.seq #[tok, tokNoHover]) == (none, .seq #[tok, tokNoHover])
#guard takeAttr "data-verso-hover" (.seq #[.text true " ", tok]) == (none, .seq #[.text true " ", tok])

-- Adjacent content inside a wrapper blocks the search.
#guard takeAttr "data-verso-hover" (.tag "a" #[] (.seq #[tok, tokNoHover])) ==
  (none, .tag "a" #[] (.seq #[tok, tokNoHover]))

-- Content without the attribute is unchanged.
#guard takeAttr "data-verso-hover" tokNoHover == (none, tokNoHover)
#guard takeAttr "data-verso-hover" (.text true "x") == (none, .text true "x")
#guard takeAttr "data-verso-hover" (.seq #[]) == (none, .seq #[])

def hlTok : Highlighted := .token ⟨.keyword none none none, "rfl"⟩
def hlTok' : Highlighted := .token ⟨.keyword none none none, "skip"⟩

-- A sequence around a single element becomes that element, through nesting and empty text.
#guard (Highlighted.seq #[hlTok]).normalize == hlTok
#guard (Highlighted.seq #[.seq #[hlTok]]).normalize == hlTok
#guard (Highlighted.seq #[.text "", hlTok, .seq #[]]).normalize == hlTok

-- Whitespace is content, and sequences with several elements keep their structure.
#guard (Highlighted.seq #[.text " ", hlTok]).normalize == .seq #[.text " ", hlTok]
#guard (Highlighted.seq #[hlTok, hlTok']).normalize == .seq #[hlTok, hlTok']

-- Normalization reaches inside spans and proof states.
#guard (Highlighted.span #[] (.seq #[hlTok])).normalize == .span #[] hlTok
#guard (Highlighted.tactics #[] 5 10 (.seq #[.text "", hlTok])).normalize ==
  .tactics #[] 5 10 hlTok

end Verso.HoverMergeTest
