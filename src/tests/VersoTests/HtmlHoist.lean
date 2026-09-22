/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

import Errata
import Plausible
import VersoManual.Html
import all VersoTests.SerializationGenerators
import all VersoManual.Html.Hoist
public meta import Verso.Output.Html
public meta import VersoManual.Html.Hoist
meta import all VersoManual.Html.Hoist
public meta import VersoManual.Html

namespace Verso.Tests.HtmlHoist

open Verso.Output
open Verso.Output.Html
open Verso.Genre.Manual.Html.Hoist
open Errata
open Plausible Gen Arbitrary

private def compact (html : Html) : String :=
  (postprocess html).asString (breakLines := false)

private def marker (label : String) : Html :=
  suppressible "margin" {{<sup>{{label}}</sup>}}

private def note (label : String) : Html :=
  hoist "margin" {{<span class="note">{{label}}</span>}}

#test_guard compact {{<p>"text"{{marker "1"}}{{note "A"}}</p>}} ==
  "<p>text<sup>1</sup><span class=\"note\">A</span></p>"

#test_guard compact {{
  <table><tr><td>"text"{{marker "1"}}{{note "A"}}</td></tr></table>
}} ==
  "<span class=\"note\">A</span><table><tr><td>text<sup>1</sup></td></tr></table>"

#test_guard compact {{
  <table><tr><td>{{note "A"}}{{note "B"}}{{note "C"}}</td></tr></table>
}} ==
  "<span class=\"note\">A</span><span class=\"note\">B</span><span class=\"note\">C</span><table><tr><td></td></tr></table>"

#test_guard compact {{
  <table>{{hoist "margin" {{<span>"A"</span><span>"B"</span>}}}}</table>
}} ==
  "<span>A</span><span>B</span><table></table>"

#test_guard compact {{<table>{{hoist "margin" {{"hoisted text"}}}}</table>}} ==
  "hoisted text<table></table>"

#test_guard compact (hoist "margin" {{"text without a barrier"}}) ==
  "text without a barrier"

#test_guard compact (.tag "span" #[
  (generatedWrapperAttr, ""),
  (hoistAttr, "margin"),
  ("class", "kept")
] (.text true "text")) ==
  "<span class=\"kept\">text</span>"

#test_guard compact (barrier "margin" false {{<div>{{note "custom"}}</div>}}) ==
  "<div></div><span class=\"note\">custom</span>"

#test_guard compact (barrier "margin" true {{<div>{{note "before"}}</div>}}) ==
  "<span class=\"note\">before</span><div></div>"

#test_guard compact (barrier "margin" false {{<table>{{note "after"}}</table>}}) ==
  "<table></table><span class=\"note\">after</span>"

#test_guard compact (noBarrier "margin" {{<table>{{note "safe"}}</table>}}) ==
  "<table><span class=\"note\">safe</span></table>"

#test_guard compact (barrier "margin" false {{
  <div><table>{{note "A"}}{{note "B"}}</table>{{note "C"}}</div>
}}) ==
  "<div><table></table></div><span class=\"note\">A</span><span class=\"note\">B</span><span class=\"note\">C</span>"

#test_guard compact (suppress "margin" {{
  <nav>{{marker "1"}}{{note "hidden"}}<span>"kept"</span></nav>
}}) ==
  "<nav><span>kept</span></nav>"

#test_guard compact (barrier "margin" false {{
  <div>
    {{note "before"}}
    {{suppress "margin" {{<span>{{note "discarded"}}{{marker "2"}}</span>}}}}
    {{note "after"}}
  </div>
}}) ==
  "<div><span></span></div><span class=\"note\">before</span><span class=\"note\">after</span>"

private def futureNote (label : String) : Html :=
  hoist "future" {{<span class="future">{{label}}</span>}}

#test_guard compact (barrier "margin" false {{
  <div>
    {{barrier "future" false {{<section>{{note "margin"}}{{futureNote "future"}}</section>}}}}
  </div>
}}) ==
  "<div><section></section><span class=\"future\">future</span></div><span class=\"note\">margin</span>"

#test_guard compact (barrier "outer" false {{
  <div>
    {{barrier "inner" false {{
      <section>{{hoist "inner" (hoist "outer" {{<span>"both"</span>}})}}</section>
    }}}}
  </div>
}}) ==
  "<div><section></section></div><span>both</span>"

#test_guard compact (barrier "first" true (barrier "second" false {{
  <div>
    {{hoist "first" {{<span>"first"</span>}}}}
    {{hoist "second" {{<span>"second"</span>}}}}
  </div>
}})) ==
  "<span>first</span><div></div><span>second</span>"

#test_guard compact (.tag "div" #[
  (hoistAttr, "none"),
  (barrierAttr, "none"),
  (barrierBeforeAttr, "none"),
  (noBarrierAttr, "none"),
  (suppressAttr, "none"),
  (suppressibleAttr, "none")
] (.text true "clean")) == "<div>clean</div>"

private def titleWithMarginalia : Html :=
  {{"Title"{{marker "1"}}{{note "title note"}}}}

private def tocEntry : Verso.Genre.Manual.Html.Toc where
  title := titleWithMarginalia
  path := #["chapter"]
  id := some "chapter"
  sectionNum := none
  children := []

#test_guard !(compact (tocEntry.html none)).contains "title note"
#test_guard !(compact (tocEntry.html none)).contains "<sup>"
#test_guard (compact titleWithMarginalia).contains "title note"
#test_guard (compact titleWithMarginalia).contains "<sup>1</sup>"

inductive HoistNesting where
  | leaf
  | group (children : Array HoistNesting)
  | barriers (kinds : Array String) (before : Bool) (child : HoistNesting)
  | noBarriers (kinds : Array String) (child : HoistNesting)
  | suppresses (kinds : Array String) (child : HoistNesting)
  | hoists (kinds : Array String) (child : HoistNesting)
  | suppressibles (kinds : Array String) (child : HoistNesting)
deriving Repr

structure HoistCase where
  html : Html
deriving Repr

def someKinds (kinds : Array String) (notEmpty : 0 < kinds.size) : Gen (Array String) := do
  let selected ← kinds.filterM fun _ => arbitrary
  if !selected.isEmpty then return selected
  let ⟨i, _, _⟩ ← chooseNatLt 0 kinds.size notEmpty
  return #[kinds[i]]

partial def hoistNesting (kinds : Array String) (notEmpty : 0 < kinds.size) : Nat → Gen HoistNesting
  | 0 => pure .leaf
  | fuel + 1 =>
    let child := hoistNesting kinds notEmpty fuel
    let selected := someKinds kinds notEmpty
    oneOf #[
      pure .leaf,
      .group <$> sizedArrayOf child,
      .barriers <$> selected <*> arbitrary <*> child,
      .noBarriers <$> selected <*> child,
      .suppresses <$> selected <*> child,
      .hoists <$> selected <*> child,
      .suppressibles <$> selected <*> child
    ] (by simp)

partial def HoistNesting.toHtml : HoistNesting → Gen Html
  | .leaf => decorativeHtml
  | .group children => do
    decorate <| .seq (← children.mapM HoistNesting.toHtml)
  | .barriers kinds before child => do
    decorate <| kinds.foldl (fun html kind => barrier kind before html) (← child.toHtml)
  | .noBarriers kinds child => do
    decorate <| kinds.foldl (fun html kind => noBarrier kind html) (← child.toHtml)
  | .suppresses kinds child => do
    decorate <| kinds.foldl (fun html kind => suppress kind html) (← child.toHtml)
  | .hoists kinds child => do
    decorate <| kinds.foldl (fun html kind => hoist kind html) (← child.toHtml)
  | .suppressibles kinds child => do
    decorate <| kinds.foldl (fun html kind => suppressible kind html) (← child.toHtml)
where
  decorativeHtml : Gen Html := arbitrary.resize (· / 4)
  decorate (html : Html) : Gen Html := do
    let contents := Html.seq #[← decorativeHtml, html, ← decorativeHtml]
    let attrs ← sizedArrayOf do return (← arbitrary, ← arbitrary)
    frequency (pure contents) [
      (2, pure contents),
      (2, pure <| .tag (← arbitrary) attrs contents),
      (1, pure <| .tag "table" attrs contents)
    ]

instance : ArbitraryFueled HoistCase where
  arbitraryFueled fuel := do
    let extraKindCount := min (← chooseNat) 2
    let baseKinds := #["kind-0"] ++ (Array.range extraKindCount).map fun i => s!"kind-{i + 1}"
    let includeMargin : Bool ← arbitrary
    let kinds := if includeMargin then baseKinds.push "margin" else baseKinds
    let nesting ← hoistNesting kinds (by
      cases includeMargin <;> simp [kinds, baseKinds] <;> omega) fuel
    return ⟨← nesting.toHtml⟩

instance : Shrinkable HoistCase where
  shrink test := Shrinkable.shrink test.html |>.map HoistCase.mk

/-- HTML hoisting reaches a fixed point after one complete post-processing pass. -/
@[test]
def postprocessIdempotent : Test := property <| ∀ test : HoistCase,
  postprocess (postprocess test.html) == postprocess test.html
