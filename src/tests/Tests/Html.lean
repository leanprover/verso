/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
meta import all Verso.Output.Html

namespace Verso.Tests.Html

open Verso.Output
open Verso.Output.Html

/-! ## Tests for HTML syntax macros -/

private def testAttrs := {{ <html charset="UTF-8" charset = "UTF-8" a="b" a-b-c="44" {{#[("x", "y")] }} /> }}

/--
info: Verso.Output.Html.tag
  "html"
  #[("charset", "UTF-8"), ("charset", "UTF-8"), ("a", "b"), ("a-b-c", "44"), ("x", "y")]
  (Verso.Output.Html.seq #[])
-/
#guard_msgs in
#eval testAttrs

private def testAttrsAntiquotes :=
  {{ <html charset={{"UTF" ++ "-8"}} "charset" = "UTF-8" a="b" a-b-c="44" {{#[("x", "y")]}} /> }}

/--
info: Verso.Output.Html.tag
  "html"
  #[("charset", "UTF-8"), ("charset", "UTF-8"), ("a", "b"), ("a-b-c", "44"), ("x", "y")]
  (Verso.Output.Html.seq #[])
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
info: Verso.Output.Html.tag
  "html"
  #[]
  (Verso.Output.Html.seq
    #[Verso.Output.Html.tag
        "head"
        #[]
        (Verso.Output.Html.seq
          #[Verso.Output.Html.tag "meta" #[("charset", "UTF-8")] (Verso.Output.Html.seq #[]),
            Verso.Output.Html.tag "script" #[] (Verso.Output.Html.seq #[])]),
      Verso.Output.Html.tag
        "body"
        #[("lang", "en"), ("class", "thing"), ("data-foo", "data foo")]
        (Verso.Output.Html.seq
          #[Verso.Output.Html.tag "input" #[("type", "checkbox"), ("checked", "")] (Verso.Output.Html.seq #[]),
            Verso.Output.Html.tag
              "p"
              #[]
              (Verso.Output.Html.seq
                #[Verso.Output.Html.text true "foo bar", Verso.Output.Html.tag "br" #[] (Verso.Output.Html.seq #[]),
                  Verso.Output.Html.text true "hey"])])])
-/
#guard_msgs in
  #eval test

private def leanKwTest : Html := {{
  <label for="foo">"Blah"</label>
}}

/-- info: Verso.Output.Html.tag "label" #[("for", "foo")] (Verso.Output.Html.text true "Blah") -/
#guard_msgs in
  #eval leanKwTest


/--
error: `<br>` doesn't allow contents

Hint: Remove contents
  <̵b̵r̵>̵"̵f̵o̵o̵"̵ ̵"̵f̵o̵o̵"̵<̵/̵b̵r̵>̵<̲b̲r̲/̲>̲
-/
#guard_msgs in
  #eval show Html from {{ <br>"foo" "foo"</br> }}

/--
info: |
<html>
  <head>
    <meta charset="UTF-8">
    <script></script>
    </head>
  <body lang="en" class="thing" data-foo="data foo">
    <input type="checkbox" checked=""><p>
      foo bar<br>hey</p>
    </body>
  </html>
-/
#guard_msgs in
  #eval IO.println <| "|\n" ++ test.asString
