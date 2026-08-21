/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Errata
import all Verso.Code.Highlighted
meta import Verso.Output.Html
meta import SubVerso.Highlighting

open SubVerso.Highlighting (Highlighted)
open Verso.Code (takeAttrs)
open Verso.Output (Html)

namespace Verso.HoverMergeTest

/-!
These helpers support merging a documented token's hover content into a message span that
shares the token's extent: `Highlighted.normalize` makes the sole-token shape recognizable,
and `takeAttrs` moves the token's hover attributes up to the span.
-/

def tok : Html := .tag "span" #[("class", "token"), ("data-verso-hover", "5")] (.text true "x")
def tokNoHover : Html := .tag "span" #[("class", "token")] (.text true "x")

-- The attribute is taken from a bare element.
#test_guard takeAttrs #["data-verso-hover"] tok == (#[("data-verso-hover", "5")], tokNoHover)

-- The attribute is found through a wrapping element, such as a link.
#test_guard takeAttrs #["data-verso-hover"] (.tag "a" #[("href", "x.html")] tok) ==
  (#[("data-verso-hover", "5")], .tag "a" #[("href", "x.html")] tokNoHover)

-- Attributes are gathered across the wrappers of a sole element: the hover from the token
-- and the extra links from the link element around it.
#test_guard takeAttrs #["data-verso-hover", "data-verso-links"]
    (.tag "a" #[("data-verso-links", "[]")] tok) ==
  (#[("data-verso-links", "[]"), ("data-verso-hover", "5")], .tag "a" #[] tokNoHover)

-- Only the attributes that are present appear in the result.
#test_guard takeAttrs #["data-verso-hover", "data-verso-links"]
    (.tag "a" #[("data-verso-links", "[]")] tokNoHover) ==
  (#[("data-verso-links", "[]")], .tag "a" #[] tokNoHover)

def tokLinked : Html :=
  .tag "span" #[("class", "token"), ("data-verso-hover", "5"), ("data-verso-links", "[2]")]
    (.text true "x")

-- Each attribute is taken from the outermost element that carries it, and repeats on
-- elements nested inside stay in place.
#test_guard takeAttrs #["data-verso-hover", "data-verso-links"]
    (.tag "a" #[("data-verso-hover", "9")] tokLinked) ==
  (#[("data-verso-hover", "9"), ("data-verso-links", "[2]")],
   .tag "a" #[] (.tag "span" #[("class", "token"), ("data-verso-hover", "5")] (.text true "x")))
#test_guard takeAttrs #["data-verso-hover", "data-verso-links"]
    (.tag "a" #[("data-verso-links", "[1]")] tokLinked) ==
  (#[("data-verso-links", "[1]"), ("data-verso-hover", "5")],
   .tag "a" #[] (.tag "span" #[("class", "token"), ("data-verso-links", "[2]")] (.text true "x")))

-- The outermost attribute wins, and inner ones are left in place.
#test_guard takeAttrs #["data-verso-hover"] (.tag "a" #[("data-verso-hover", "9")] tok) ==
  (#[("data-verso-hover", "9")], .tag "a" #[] tok)

-- Empty content around a sole element does not block the search.
#test_guard takeAttrs #["data-verso-hover"] (.seq #[.text true "", tok, .seq #[]]) ==
  (#[("data-verso-hover", "5")], tokNoHover)

-- Adjacent content blocks the search, including whitespace.
#test_guard takeAttrs #["data-verso-hover"] (.seq #[tok, .text true "y"]) ==
  (#[], .seq #[tok, .text true "y"])
#test_guard takeAttrs #["data-verso-hover"] (.seq #[tok, tokNoHover]) == (#[], .seq #[tok, tokNoHover])
#test_guard takeAttrs #["data-verso-hover"] (.seq #[.text true " ", tok]) ==
  (#[], .seq #[.text true " ", tok])

-- Adjacent content inside a wrapper blocks the search.
#test_guard takeAttrs #["data-verso-hover"] (.tag "a" #[] (.seq #[tok, tokNoHover])) ==
  (#[], .tag "a" #[] (.seq #[tok, tokNoHover]))

-- Content without the attributes is unchanged.
#test_guard takeAttrs #["data-verso-hover"] tokNoHover == (#[], tokNoHover)
#test_guard takeAttrs #["data-verso-hover"] (.text true "x") == (#[], .text true "x")
#test_guard takeAttrs #["data-verso-hover"] (.seq #[]) == (#[], .seq #[])

def hlTok : Highlighted := .token ⟨.keyword none none none, "rfl"⟩
def hlTok' : Highlighted := .token ⟨.keyword none none none, "skip"⟩

-- A sequence around a single element becomes that element, through nesting and empty text.
#test_guard (Highlighted.seq #[hlTok]).normalize == hlTok
#test_guard (Highlighted.seq #[.seq #[hlTok]]).normalize == hlTok
#test_guard (Highlighted.seq #[.text "", hlTok, .seq #[]]).normalize == hlTok

-- Whitespace is content, and sequences with several elements keep their structure.
#test_guard (Highlighted.seq #[.text " ", hlTok]).normalize == .seq #[.text " ", hlTok]
#test_guard (Highlighted.seq #[hlTok, hlTok']).normalize == .seq #[hlTok, hlTok']

-- Normalization reaches inside spans and proof states.
#test_guard (Highlighted.span #[] (.seq #[hlTok])).normalize == .span #[] hlTok
#test_guard (Highlighted.tactics #[] 5 10 (.seq #[.text "", hlTok])).normalize ==
  .tactics #[] 5 10 hlTok

end Verso.HoverMergeTest
