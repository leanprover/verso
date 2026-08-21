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

/-! ## Tests for escaping -/

/-- info: "<p>x &amp; y &amp;lt; &lt;z&gt;</p>" -/
#guard_msgs in
  #eval Html.asString {{ <p>"x & y &lt; <z>"</p> }} (breakLines := false)

/-- info: "<p>x & y &lt; <em>z</em></p>" -/
#guard_msgs in
  #eval Html.asString (.tag "p" #[] (.text false "x & y &lt; <em>z</em>")) (breakLines := false)

/-- info: "<p class=\"a&amp;b&quot;c\">x</p>" -/
#guard_msgs in
  #eval Html.asString {{ <p class="a&b\"c">"x"</p> }} (breakLines := false)

/-! ## Tests for URL rewriting -/

private def urlCases : Array String :=
  #["/x", "./x", "../x", "-verso-data/x", "#frag", "https://x", "//cdn/x", "mailto:x", ""]

private def urlDoc : Array Html :=
    urlCases.map (fun u => {{<a href={{u}}>"link"</a>}}) ++
    #[{{<base href="/root/"/>}},
      {{<a href="/remote/x" data-verso-remote="true">"remote"</a>}},
      {{<img src="/img.png"/>}},
      {{<object data="/object"/>}},
      {{<video poster="/poster.png"></video>}},
      {{<img srcset="/a.png 1x, /b.png 2x"/>}},
      {{<link rel="preload" imagesrcset="/c.png 480w"/>}},
      {{<form action="/submit"></form>}},
      {{<button formaction="/send"></button>}},
      {{<blockquote cite="/source"></blockquote>}},
      {{<a ping="/one /two">"ping"</a>}},
      {{<a title="/not-a-url">"kept"</a>}}]

/--
info: |
<a href="[/x]">link</a>
<a href="[./x]">link</a>
<a href="[../x]">link</a>
<a href="[-verso-data/x]">link</a>
<a href="[#frag]">link</a>
<a href="[https://x]">link</a>
<a href="[//cdn/x]">link</a>
<a href="[mailto:x]">link</a>
<a href="[]">link</a>
<base href="/root/">
<a href="/remote/x" data-verso-remote="true">remote</a>
<img src="[/img.png]">
<object data="[/object]"></object>
<video poster="[/poster.png]"></video>
<img srcset="[/a.png] 1x, [/b.png] 2x">
<link rel="preload" imagesrcset="[/c.png] 480w">

<form action="[/submit]"></form>
<button formaction="[/send]"></button>
<blockquote cite="[/source]"></blockquote>
<a ping="[/one] [/two]">ping</a>
<a title="/not-a-url">kept</a>
-/
#guard_msgs in
#eval do
  IO.println "|"
  for html in (urlDoc.map <| rewriteUrls ("[" ++ · ++ "]")) do
    IO.println html.asString

/-! ## Tests for the URL-list attribute parsers -/

private def mark (url : String) : String := "<" ++ url ++ ">"

/--
Cases for `rewriteSrcset`. A candidate's URL ends at whitespace or a trailing comma, never at a
comma inside the URL, and every separator, descriptor, and piece of whitespace survives untouched.
-/
private def srcsetCases : Array String := #[
  -- ordinary lists
  "a.png",
  "a.png 1x",
  "a.png 1x, b.png 2x",
  "a.png 480w, b.png 800w, c.png",
  -- a URL containing a comma is one URL, because only a trailing comma ends a candidate
  "a,b.png 1x, c.png",
  "data:image/png;base64,AAAA 1x",
  -- commas as the only separator, with no space after them
  "a.png,b.png",
  "a.png 1x,b.png 2x",
  -- odd but legal whitespace and separators
  "   a.png   1x   ,   b.png   2x   ",
  ",,, a.png 1x ,,, b.png 2x ,,,",
  "\na.png\t1x,\nb.png\t2x\n",
  -- degenerate inputs
  "",
  "   ",
  ",",
  ",,,",
  -- a descriptor holding a comma inside parentheses
  "a.png (min-width, 100px), b.png 2x",
  -- trailing comma with no candidate after it
  "a.png 1x,",
  "a.png,"
]

/--
info: |
"a.png" => "<a.png>"
"a.png 1x" => "<a.png> 1x"
"a.png 1x, b.png 2x" => "<a.png> 1x, <b.png> 2x"
"a.png 480w, b.png 800w, c.png" => "<a.png> 480w, <b.png> 800w, <c.png>"
"a,b.png 1x, c.png" => "<a,b.png> 1x, <c.png>"
"data:image/png;base64,AAAA 1x" => "<data:image/png;base64,AAAA> 1x"
"a.png,b.png" => "<a.png,b.png>"
"a.png 1x,b.png 2x" => "<a.png> 1x,<b.png> 2x"
"   a.png   1x   ,   b.png   2x   " => "   <a.png>   1x   ,   <b.png>   2x   "
",,, a.png 1x ,,, b.png 2x ,,," => ",,, <a.png> 1x ,,, <b.png> 2x ,,,"
"\na.png\t1x,\nb.png\t2x\n" => "\n<a.png>\t1x,\n<b.png>\t2x\n"
"" => ""
"   " => "   "
"," => ","
",,," => ",,,"
"a.png (min-width, 100px), b.png 2x" => "<a.png> (min-width, 100px), <b.png> 2x"
"a.png 1x," => "<a.png> 1x,"
"a.png," => "<a.png>,"
-/
#guard_msgs in
  #eval IO.println <| "|\n" ++ String.join
    (srcsetCases.toList.map fun c => s!"{repr c} => {repr (Html.rewriteSrcset mark c)}\n")

/-- Cases for `rewriteUrlList`, which `ping` uses. -/
private def urlListCases : Array String :=
  #["a", "a b", "  a   b  ", "", "   ", "\ta\nb\t"]

/--
info: |
"a" => "<a>"
"a b" => "<a> <b>"
"  a   b  " => "  <a>   <b>  "
"" => ""
"   " => "   "
"\ta\nb\t" => "\t<a>\n<b>\t"
-/
#guard_msgs in
  #eval IO.println <| "|\n" ++ String.join
    (urlListCases.toList.map fun c => s!"{repr c} => {repr (Html.rewriteUrlList mark c)}\n")
