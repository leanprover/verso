/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Std.Tactic.GuardMsgs

import LeanDoc.Doc
import LeanDoc.Examples
import LeanDoc.Html
import LeanDoc.Method


namespace LeanDoc.Doc.Html

open LeanDoc Doc Html


class ToHtml (α : Type u) where
  toHtml : α → Array Html

section
open ToHtml

defmethod LinkDest.str : LinkDest → String
  | .url addr => addr
  | .ref TODO => TODO

defmethod Array.flatten (xs : Array (Array α)) : Array α := Id.run do
  let mut out := #[]
  for x in xs do out := out ++ x
  pure out

partial def Inline.toHtml : Inline → Array Html
  | .text str => #[str]
  | .link content dest => #[{{ <a href={{ dest.str }}> {{ content.map toHtml |>.flatten }}* </a> }}]
  | .linebreak _str => #[]
  | .emph content => #[{{ <em> {{ content.map toHtml |>.flatten }}* </em>}}]
  | .bold content => #[{{ <strong> {{ content.map toHtml |>.flatten }}* </strong>}}]
  | .code str => #[{{ <code> {{str}} </code>}}]
  | .concat inlines => inlines.map toHtml |>.flatten

instance : ToHtml Inline where
  toHtml := Inline.toHtml


partial def Block.toHtml : Block → Array Html
  | .para xs => #[{{ <p> {{ xs.map Inline.toHtml |>.flatten }}* </p> }}]
  | .blockquote bs => #[{{ <blockquote> {{ bs.map Block.toHtml |>.flatten }}* </blockquote> }}]
  | .ul items => #[{{ <ul> {{ items.map fun li => {{ <li> {{ li.contents.map Block.toHtml |>.flatten }}* </li>}} }}* </ul> }}]
  | .code (some name) _ _ content => #[{{ <pre class={{"language-" ++ name}}> {{ content }} </pre>}}]
  | .code none _ _ content => #[{{ <pre> {{ content }} </pre>}}]


instance : ToHtml Block where
  toHtml := Block.toHtml

partial def Part.toHtml (p : Part) (level : Nat) : Array Html := #[{{
  <section>
    {{ #[.tag s!"h{level+1}" #[] (p.title.map ToHtml.toHtml |>.flatten)] ++ (p.content.map ToHtml.toHtml).flatten ++ (p.subParts.map (Part.toHtml · (level + 1))).flatten }}*
  </section>
}}]

instance : ToHtml Part where
  toHtml p := Part.toHtml p 0

open LeanDoc.Examples

/--
info: #[LeanDoc.Html.tag
    "section"
    #[]
    #[LeanDoc.Html.tag "h1" #[] #[LeanDoc.Html.text "More writing"],
      LeanDoc.Html.tag
        "section"
        #[]
        #[LeanDoc.Html.tag "h2" #[] #[LeanDoc.Html.text "Section 1"],
          LeanDoc.Html.tag "p" #[] #[LeanDoc.Html.text "Here's some code"],
          LeanDoc.Html.tag
            "pre"
            #[]
            #[LeanDoc.Html.text "(define (zero f z) z)\n(define (succ n) (lambda (f x) (f (n f z))))\n"]]]]
-/
#guard_msgs in
  #eval toHtml e
end

def embody (content : Array Html) : Html := {{
<html>
<head></head>
<body> {{ content }}* </body>
</html>
}}
