import Std.Tactic.GuardMsgs

import LeanDoc.Doc
import LeanDoc.Examples
import LeanDoc.Html
import LeanDoc.Method


namespace LeanDoc.Doc.Html

open LeanDoc Doc Html


class ToHtml (α : Type u) where
  toHtml : α → Html

section
open ToHtml

defmethod LinkDest.str : LinkDest → String
  | .url addr => addr
  | .ref TODO => TODO

partial def Inline.toHtml : Inline → Html
  | .text str => str
  | .link content dest => {{ <a href={{ dest.str }}> {{ content.map toHtml }}* </a> }}
  | .linebreak _str => {{ <br /> }} -- this is more like Github Flavored - we don't actually want that here but it was expedient
  | .emph content => {{ <emph> {{ content.map toHtml }}* </emph>}}
  | .bold content => {{ <strong> {{ content.map toHtml }}* </strong>}}

instance : ToHtml Inline where
  toHtml := Inline.toHtml


partial def Block.toHtml : Block → Html
  | .para xs => {{ <p> {{ xs.map Inline.toHtml }}* </p> }}
  | .blockquote bs => {{ <blockquote> {{ bs.map Block.toHtml }}* </blockquote> }}
  | .ul items => {{ <ul> {{ items.map fun li => {{ <li> {{ li.contents.map Block.toHtml }}* </li>}} }}* </ul> }}
  | .code (some name) _ _ content => {{ <pre class={{"language-" ++ name}}> {{ content }} </pre>}}
  | .code none _ _ content => {{ <pre> {{ content }} </pre>}}


instance : ToHtml Block where
  toHtml := Block.toHtml

partial def Part.toHtml (p : Part) (level : Nat) : Html := {{
  <section>
    {{ #[.tag s!"h{level+1}" #[] (p.title.map ToHtml.toHtml)] ++ p.content.map ToHtml.toHtml ++ p.subParts.map (Part.toHtml · (level + 1)) }}*
  </section>
}}

instance : ToHtml Part where
  toHtml p := Part.toHtml p 0

open LeanDoc.Examples

/--
info: LeanDoc.Html.tag
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
          #[LeanDoc.Html.text "(define (zero f z) z)\n(define (succ n) (lambda (f x) (f (n f z))))\n"]]]
-/
#guard_msgs in
  #eval toHtml e
end

def embody (content : Html) : Html := {{
<html>
<head></head>
<body> {{ content }} </body>
</html>
}}
