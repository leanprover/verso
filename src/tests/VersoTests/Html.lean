/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Errata
meta import all Verso.Output.Html

namespace Verso.Tests.Html

open Lean (Html)
open Verso.Output.Html

/-! ## Tests for HTML syntax macros -/

private def testAttrs := {{ <html charset="UTF-8" charset = "UTF-8" a="b" a-b-c="44" {{#[("x", "y")] }} /> }}

/-- info: Html.element "html" #[("charset", "UTF-8"), ("charset", "UTF-8"), ("a", "b"), ("a-b-c", "44"), ("x", "y")] (seq #[]) -/

#test_msgs in
#eval testAttrs

private def testAttrsAntiquotes :=
  {{ <html charset={{"UTF" ++ "-8"}} "charset" = "UTF-8" a="b" a-b-c="44" {{#[("x", "y")]}} /> }}

/-- info: Html.element "html" #[("charset", "UTF-8"), ("charset", "UTF-8"), ("a", "b"), ("a-b-c", "44"), ("x", "y")] (seq #[]) -/

#test_msgs in
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
info: Html.element "html" #[]
  (seq
    #[Html.element "head" #[]
        (seq #[Html.element "meta" #[("charset", "UTF-8")] (seq #[]), Html.element "script" #[] (seq #[])]),
      Html.element "body" #[("lang", "en"), ("class", "thing"), ("data-foo", "data foo")]
        (seq
          #[Html.element "input" #[("type", "checkbox"), ("checked", "")] (seq #[]),
            Html.element "p" #[] (seq #[Html.text "foo bar", Html.element "br" #[] (seq #[]), Html.text "hey"])])])
-/

#test_msgs in
  #eval test

private def leanKwTest : Html := {{
  <label for="foo">"Blah"</label>
}}

/-- info: Html.element "label" #[("for", "foo")] (Html.text "Blah") -/

#test_msgs in
  #eval leanKwTest


/--
error: `<br>` doesn't allow contents

Hint: Remove contents
  <̵b̵r̵>̵"̵f̵o̵o̵"̵ ̵"̵f̵o̵o̵"̵<̵/̵b̵r̵>̵<̲b̲r̲/̲>̲
-/
#test_msgs in
  #eval show Html from {{ <br>"foo" "foo"</br> }}
