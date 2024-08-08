/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc
import Verso.Output.Html
import Verso.Method
import Verso.Code.Highlighted

set_option guard_msgs.diff true

namespace Verso.Doc.Html

open Verso Output Doc Html
open Verso.Code (HighlightHtmlM)
open Verso.Code.Hover

structure Options (g : Genre) (m : Type → Type) where
  /-- The level of the top-level headers -/
  headerLevel : Nat := 1
  logError : String → m Unit

def Options.reinterpret (lift : {α : _} → m α → m' α) (opts : Options g m) : Options g m' :=
  {opts with
    logError := fun msg => lift <| opts.logError msg}

def Options.lift [MonadLiftT m m'] (opts : Options g m) : Options g m' :=
  opts.reinterpret MonadLiftT.monadLift

abbrev HtmlT (genre : Genre) (m : Type → Type) : Type → Type :=
  ReaderT (Options genre m × genre.TraverseContext × genre.TraverseState) (StateT (Dedup Html) m)

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

instance [Monad m] : MonadLift HighlightHtmlM (HtmlT genre m) where
  monadLift act := modifyGet act

open HtmlT

class ToHtml (genre : Genre) (m : Type → Type) (α : Type u) where
  toHtml (val : α) : HtmlT genre m Html

class GenreHtml (genre : Genre) (m : Type → Type) where
  part
    (partHtml : Part genre → Array (String × String) → HtmlT genre m Html)
    (metadata : genre.PartMetadata) (contents : Part genre) : HtmlT genre m Html
  block
    (inlineHtml : Inline genre → HtmlT genre m Html)
    (blockHtml : Block genre → HtmlT genre m Html)
    (container : genre.Block) (contents : Array (Block genre)) : HtmlT genre m Html
  inline
    (inlineHtml : Inline genre → HtmlT genre m Html)
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
  | .code content => pure #[{{ <pre> {{ content }} </pre>}}]
  | .concat items => Html.seq <$> items.mapM Block.toHtml
  | .other container content => GenreHtml.block Inline.toHtml Block.toHtml container content


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
  block _ _ x := nomatch x
  inline _ x := nomatch x

defmethod Genre.toHtml (g : Genre) [ToHtml g m α] (options : Options g m) (context : g.TraverseContext) (state : g.TraverseState) (x : α) : StateT (Dedup Html) m Html :=
  ToHtml.toHtml x (options, context, state)
