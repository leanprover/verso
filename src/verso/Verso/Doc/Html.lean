/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc
import Verso.Examples
import Verso.Output.Html
import Verso.Method


namespace Verso.Doc.Html

open Verso Output Doc Html

structure Options (g : Genre) (m : Type → Type) where
  /-- The level of the top-level headers -/
  headerLevel : Nat := 1
  logError : String → m Unit

abbrev HtmlT (genre : Genre) (m : Type → Type) : Type → Type :=
  ReaderT (Options genre m × genre.TraverseContext × genre.TraverseState) m

instance [Functor m] : Functor (HtmlT genre m) where
  map f act := fun ρ => Functor.map f (act ρ)

instance [Monad m] : Monad (HtmlT genre m) where
  pure x := fun _ => pure x
  bind act k := fun ρ => (act ρ >>= fun x => k x ρ)

instance [Pure m] : MonadReader (Options genre m × genre.TraverseContext × genre.TraverseState) (HtmlT genre m) where
  read := fun ρ => pure ρ

instance : MonadWithReader (Options genre m × genre.TraverseContext × genre.TraverseState) (HtmlT genre m) where
  withReader f act := fun ρ => act (f ρ)

def HtmlT.options [Monad m] : HtmlT genre m (Options genre m) := do
  let (opts, _, _) ← read
  pure opts

def HtmlT.withOptions (opts : Options g m → Options g m) (act : HtmlT g m α) : HtmlT g m α :=
  withReader (fun (x, y, z) => (opts x, y, z)) act

def HtmlT.context [Monad m] : HtmlT genre m genre.TraverseContext := do
  let (_, ctxt, _) ← read
  pure ctxt

def HtmlT.state [Monad m] : HtmlT genre m genre.TraverseState := read >>= fun (_, _, state) => pure state

def HtmlT.logError [Monad m] (message : String) : HtmlT genre m Unit := do (← options).logError message

open HtmlT

class ToHtml (genre : Genre) (m : Type → Type) (α : Type u) where
  toHtml (val : α) : HtmlT genre m Html

class GenreHtml (genre : Genre) (m : Type → Type) where
  part (partHtml : Part genre → Array (String × String) → HtmlT genre m Html)
    (metadata : genre.PartMetadata) (contents : Part genre) : HtmlT genre m Html
  block (blockHtml : Block genre → HtmlT genre m Html)
    (container : genre.Block) (contents : Array (Block genre)) : HtmlT genre m Html
  inline (inlineHtml : Inline genre → HtmlT genre m Html)
    (container : genre.Inline) (contents : Array (Inline genre)) : HtmlT genre m Html


section
open ToHtml

partial def Inline.toHtml [Monad m] [GenreHtml g m] : Inline g → HtmlT g m Html
  | .text str => pure <| .text true str
  | .link content dest => do
    pure {{ <a href={{dest}}> {{← content.mapM toHtml}} </a> }}
  | .image alt dest => do
    pure {{ <img src={{dest}} alt={{alt}}/> }}
  | .footnote name content => do
      pure {{ <details class="footnote"><summary>"["{{name}}"]"</summary>{{← content.mapM toHtml}}</details>}}
  | .linebreak str => pure <| Html.text false str
  | .emph content => do
    pure {{ <em> {{← content.mapM toHtml }} </em> }}
  | .bold content => do
    pure {{ <strong> {{← content.mapM toHtml}} </strong> }}
  | .code str => pure {{ <code> {{str}} </code> }}
  | .math mode str => do
     let classes := "math " ++ match mode with | .inline => "inline" | .display => "display"
     pure {{ <code class={{classes}}>{{str}}</code> }}
  | .concat inlines => inlines.mapM toHtml
  | .other container content => GenreHtml.inline Inline.toHtml container content

instance [Monad m] [GenreHtml g m] : ToHtml g m (Inline g) where
  toHtml := Inline.toHtml


partial def Block.toHtml [Monad m] [GenreHtml g m] : Block g → HtmlT g m Html
  | .para xs => do
    pure {{ <p> {{← xs.mapM Inline.toHtml }} </p> }}
  | .blockquote bs => do
    pure {{ <blockquote> {{← bs.mapM Block.toHtml }} </blockquote> }}
  | .ul items => do
    pure {{ <ul> {{← items.mapM fun li => do pure {{ <li> {{← li.contents.mapM Block.toHtml }} </li>}} }} </ul> }}
  | .ol start items => do
    pure {{ <ol start={{max start 0 |> toString}}> {{← items.mapM fun li => do pure {{ <li> {{← li.contents.mapM Block.toHtml }} </li>}} }} </ol> }}
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


instance [Monad m] [GenreHtml g m] : ToHtml g m (Block g) where
  toHtml := Block.toHtml

partial def Part.toHtml [Monad m] [GenreHtml g m]
    (p : Part g) (headerAttrs : Array (String × String) := #[]) : HtmlT g m Html :=
  match p.metadata with
  | .none => do
    pure {{
      <section>
        {{ .tag s!"h{(← options).headerLevel}" headerAttrs (.seq <| ← p.title.mapM ToHtml.toHtml ) }}
        {{← p.content.mapM ToHtml.toHtml  }}
        {{← withOptions (fun o => {o with headerLevel := o.headerLevel + 1}) <| p.subParts.mapM Part.toHtml }}
      </section>
    }}
  | some m =>
    GenreHtml.part (fun p attrs => Part.toHtml p attrs) m p.withoutMetadata

instance [Monad m] [GenreHtml g m] : ToHtml g m (Part g) where
  toHtml p := Part.toHtml p

instance : GenreHtml .none m where
  part _ m := nomatch m
  block _ x := nomatch x
  inline _ x := nomatch x

defmethod Genre.toHtml (g : Genre) [ToHtml g m α] (options : Options g m) (context : g.TraverseContext) (state : g.TraverseState) (x : α) : m Html :=
  ToHtml.toHtml x (options, context, state)

open Verso.Examples

/--
info: Verso.Output.Html.tag
  "section"
  #[]
  (Verso.Output.Html.seq
    #[Verso.Output.Html.tag "h1" #[] (Verso.Output.Html.seq #[Verso.Output.Html.text true "More writing"]),
      Verso.Output.Html.tag
        "section"
        #[]
        (Verso.Output.Html.seq
          #[Verso.Output.Html.tag "h2" #[] (Verso.Output.Html.seq #[Verso.Output.Html.text true "Section 1"]),
            Verso.Output.Html.tag "p" #[] (Verso.Output.Html.seq #[Verso.Output.Html.text true "Here's some code"]),
            Verso.Output.Html.tag
              "pre"
              #[]
              (Verso.Output.Html.text true "(define (zero f z) z)\n(define (succ n) (lambda (f x) (f (n f z))))\n")])])
-/
#guard_msgs in
  #eval Genre.none.toHtml (m:=Id) {logError := fun _ => ()} () () e
end

def embody (content : Html) : Html := {{
<html>
<head></head>
<body> {{ content }} </body>
</html>
}}
