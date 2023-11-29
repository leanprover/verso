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

abbrev HtmlM (genre : Genre) (α : Type) : Type :=
  ReaderT (Options × genre.TraverseContext × genre.TraverseState) Id α

def HtmlM.options : HtmlM genre Options := (·.fst) <$> read
def HtmlM.withOptions (opts : Options → Options) (act : HtmlM g α) : HtmlM g α :=
  withReader (fun (x, y, z) => (opts x, y, z)) act

def HtmlM.context : HtmlM genre genre.TraverseContext := read >>= fun (_, ctxt, _) => pure ctxt
def HtmlM.state : HtmlM genre genre.TraverseState := read >>= fun (_, _, state) => pure state

open HtmlM

class ToHtml (genre : Genre) (α : Type u) where
  toHtml (val : α) : HtmlM genre Html

class GenreHtml (genre : Genre) where
  part (partHtml : Part genre → HtmlM genre Html)
    (metadata : genre.PartMetadata) (contents : Part genre) : HtmlM genre Html
  block (blockHtml : Block genre → HtmlM genre Html)
    (container : genre.Block) (contents : Array (Block genre)) : HtmlM genre Html
  inline (inlineHtml : Inline genre → HtmlM genre Html)
    (container : genre.Inline) (contents : Array (Inline genre)) : HtmlM genre Html


section
open ToHtml

defmethod LinkDest.str : LinkDest → String
  | .url addr => addr
  | .ref TODO => TODO

partial def Inline.toHtml [GenreHtml g] : Inline g → HtmlM g Html
  | .text str => pure <| .text str
  | .link content dest => do
    pure #[{{ <a href={{ dest.str }}> {{← content.mapM toHtml}} </a> }}]
  | .linebreak _str => pure .empty
  | .emph content => do
    pure #[{{ <em> {{← content.mapM toHtml }} </em>}}]
  | .bold content => do
    pure #[{{ <strong> {{← content.mapM toHtml}} </strong>}}]
  | .code str => pure #[{{ <code> {{str}} </code>}}]
  | .concat inlines => inlines.mapM toHtml
  | .other container content => GenreHtml.inline Inline.toHtml container content

instance [GenreHtml g] : ToHtml g (Inline g) where
  toHtml := Inline.toHtml


partial def Block.toHtml [GenreHtml g] : Block g → HtmlM g Html
  | .para xs => do
    pure {{ <p> {{← xs.mapM Inline.toHtml }} </p> }}
  | .blockquote bs => do
    pure {{ <blockquote> {{← bs.mapM Block.toHtml }} </blockquote> }}
  | .ul items => do
    pure {{ <ul> {{← items.mapM fun li => do pure {{ <li> {{← li.contents.mapM Block.toHtml }} </li>}} }} </ul> }}
  | .dl items => do
    pure {{
      <dl>
        {{← items.mapM fun ⟨t, d⟩ => do
          pure {{
            <dt>{{← t.mapM Inline.toHtml }}</dt>
            <dd>{{← d.mapM Block.toHtml }}</dd>
          }}
        }}
      </dl>
    }}
  | .code (some name) _ _ content => do
    pure #[{{ <pre class={{"language-" ++ name}}> {{ content }} </pre>}}]
  | .code none _ _ content => pure #[{{ <pre> {{ content }} </pre>}}]
  | .concat items => Html.seq <$> items.mapM Block.toHtml
  | .other container content => GenreHtml.block Block.toHtml container content


instance [GenreHtml g] : ToHtml g (Block g) where
  toHtml := Block.toHtml

partial def Part.toHtml [GenreHtml g] (p : Part g) : HtmlM g Html :=
  match p.metadata with
  | .none => do
    pure {{
      <section>
        {{ .tag s!"h{(← options).headerLevel}" #[] (.seq <| ← p.title.mapM ToHtml.toHtml ) }}
        {{← p.content.mapM ToHtml.toHtml  }}
        {{← withOptions (fun o => {o with headerLevel := o.headerLevel + 1}) <| p.subParts.mapM Part.toHtml }}
      </section>
    }}
  | some m =>
    GenreHtml.part Part.toHtml m p.withoutMetadata

instance [GenreHtml g] : ToHtml g (Part g) where
  toHtml := Part.toHtml

instance : GenreHtml .none where
  part _ m := nomatch m
  block _ x := nomatch x
  inline _ x := nomatch x

defmethod Genre.toHtml (g : Genre) [ToHtml g α] (options : Options) (context : g.TraverseContext) (state : g.TraverseState) (x : α) : Html :=
  ToHtml.toHtml x (options, context, state)

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
  #eval Genre.none.toHtml {} () () e
end

def embody (content : Html) : Html := {{
<html>
<head></head>
<body> {{ content }} </body>
</html>
}}
