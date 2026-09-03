/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Verso.Output.Html
meta import Verso.Output.Html

namespace Verso.Tests.Html

open Lean (Html)
open Verso.Output.Html

/-! ## Tests for HTML syntax macros -/

private def testAttrs := {{ <html charset="UTF-8" charset = "UTF-8" a="b" a-b-c="44" {{#[("x", "y")] }} /> }}

/--
info: Lean.Html.element
  "html"
  #[("charset", "UTF-8"), ("charset", "UTF-8"), ("a", "b"), ("a-b-c", "44"), ("x", "y")]
  (Lean.Html.seq #[])
-/
#guard_msgs in
#eval testAttrs

private def testAttrsAntiquotes :=
  {{ <html charset={{"UTF" ++ "-8"}} "charset" = "UTF-8" a="b" a-b-c="44" {{#[("x", "y")]}} /> }}

/--
info: Lean.Html.element
  "html"
  #[("charset", "UTF-8"), ("charset", "UTF-8"), ("a", "b"), ("a-b-c", "44"), ("x", "y")]
  (Lean.Html.seq #[])
-/
#guard_msgs in
#eval testAttrsAntiquotes

private def test : Html := {{
  <html>
  <head>
    <!-- Set the contents -->
    <meta charset="UTF-8"/>
    <script></script>
  </head>
  <body lang="en" class="thing" data-foo="data foo">
  <input type="checkbox" checked />
  <p> "foo bar" <br/> "hey" </p>
  </body>
  </html>
}}

/--
info: Lean.Html.element
  "html"
  #[]
  (Lean.Html.seq
    #[Lean.Html.element
        "head"
        #[]
        (Lean.Html.seq
          #[Lean.Html.element "meta" #[("charset", "UTF-8")] (Lean.Html.seq #[]),
            Lean.Html.element "script" #[] (Lean.Html.seq #[])]),
      Lean.Html.element
        "body"
        #[("lang", "en"), ("class", "thing"), ("data-foo", "data foo")]
        (Lean.Html.seq
          #[Lean.Html.element "input" #[("type", "checkbox"), ("checked", "")] (Lean.Html.seq #[]),
            Lean.Html.element
              "p"
              #[]
              (Lean.Html.seq
                #[Lean.Html.text "foo bar", Lean.Html.element "br" #[] (Lean.Html.seq #[]), Lean.Html.text "hey"])])])
-/
#guard_msgs in
  #eval test

private def leanKwTest : Html := {{
  <label for="foo">"Blah"</label>
}}

/-- info: Lean.Html.element "label" #[("for", "foo")] (Lean.Html.text "Blah") -/
#guard_msgs in
  #eval leanKwTest


/--
error: `<br>` doesn't allow contents

Hint: Remove contents
  <̵b̵r̵>̵"̵f̵o̵o̵"̵ ̵"̵f̵o̵o̵"̵<̵/̵b̵r̵>̵<̲b̲r̲/̲>̲
-/
#guard_msgs in
  #eval show Html from {{ <br>"foo" "foo"</br> }}
