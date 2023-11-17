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

structure Options where
  /-- The level of the top-level headers -/
  headerLevel : Nat := 1

class ToHtml (α : Type u) where
  toHtml (options : Options) : α → Html

section
open ToHtml

defmethod LinkDest.str : LinkDest → String
  | .url addr => addr
  | .ref TODO => TODO

partial def Inline.toHtml (options : Options) : Inline → Html
  | .text str => .text str
  | .link content dest => #[{{ <a href={{ dest.str }}> {{ content.map (toHtml options) }} </a> }}]
  | .linebreak _str => .empty
  | .emph content => #[{{ <em> {{ content.map (toHtml options) }} </em>}}]
  | .bold content => #[{{ <strong> {{ content.map (toHtml options) }} </strong>}}]
  | .code str => #[{{ <code> {{str}} </code>}}]
  | .concat inlines => inlines.map (toHtml options)

instance : ToHtml Inline where
  toHtml := Inline.toHtml


partial def Block.toHtml (options : Options) : Block → Html
  | .para xs => {{ <p> {{ xs.map (Inline.toHtml options) }} </p> }}
  | .blockquote bs => {{ <blockquote> {{ bs.map (Block.toHtml options) }} </blockquote> }}
  | .ul items => {{ <ul> {{ items.map fun li => {{ <li> {{ li.contents.map (Block.toHtml options)  }} </li>}} }} </ul> }}
  | .code (some name) _ _ content => #[{{ <pre class={{"language-" ++ name}}> {{ content }} </pre>}}]
  | .code none _ _ content => #[{{ <pre> {{ content }} </pre>}}]


instance : ToHtml Block where
  toHtml := Block.toHtml

partial def Part.toHtml (options : Options) (p : Part) : Html := {{
  <section>
    {{ .tag s!"h{options.headerLevel}" #[] (.seq <| p.title.map (ToHtml.toHtml options) ) }}
    {{ p.content.map (ToHtml.toHtml options)  }}
    {{ p.subParts.map (Part.toHtml {options with headerLevel := options.headerLevel + 1}) }}
  </section>
}}

instance : ToHtml Part where
  toHtml := Part.toHtml

open LeanDoc.Examples

/--
info: LeanDoc.Html.tag
  "section"
  #[]
  (LeanDoc.Html.seq
    #[LeanDoc.Html.tag "h1" #[] (LeanDoc.Html.seq #[LeanDoc.Html.text "More writing"]),
      LeanDoc.Html.tag
        "section"
        #[]
        (LeanDoc.Html.seq
          #[LeanDoc.Html.tag "h2" #[] (LeanDoc.Html.seq #[LeanDoc.Html.text "Section 1"]),
            LeanDoc.Html.tag "p" #[] (LeanDoc.Html.seq #[LeanDoc.Html.text "Here's some code"]),
            LeanDoc.Html.tag
              "pre"
              #[]
              (LeanDoc.Html.text "(define (zero f z) z)\n(define (succ n) (lambda (f x) (f (n f z))))\n")])])
-/
#guard_msgs in
  #eval toHtml {} e
end

def embody (content : Array Html) : Html := {{
<html>
<head></head>
<body> {{ content }} </body>
</html>
}}
