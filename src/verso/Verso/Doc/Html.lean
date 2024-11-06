/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc
import Verso.Examples
import Verso.Output.Html
import Verso.Method
import Verso.Code.Highlighted

set_option guard_msgs.diff true

namespace Verso.Doc.Html

open Verso Output Doc Html
open Verso.Code (HighlightHtmlM)

structure Options (g : Genre) (m : Type → Type) where
  /-- The level of the top-level headers -/
  headerLevel : Nat := 1
  logError : String → m Unit

def Options.reinterpret (lift : {α : _} → m α → m' α) (opts : Options g m) : Options g m' :=
  {opts with
    logError := fun msg => lift <| opts.logError msg}

def Options.lift [MonadLiftT m m'] (opts : Options g m) : Options g m' :=
  opts.reinterpret MonadLiftT.monadLift

structure HtmlT.Context (genre : Genre) (m : Type → Type) where
  options : Options genre m
  traverseContext : genre.TraverseContext
  traverseState : genre.TraverseState
  /--
  If this name is defined while rendering this HTML, what ID should be placed on the defining
  occurrence for later cross-referencing?
  -/
  definitionIds : Lean.NameMap String
  linkTargets : Code.LinkTargets
  codeOptions : Code.HighlightHtmlM.Options

abbrev HtmlT (genre : Genre) (m : Type → Type) : Type → Type :=
  ReaderT (HtmlT.Context genre m) (StateT (Verso.Code.Hover.State Html) m)

def HtmlT.options [Monad m] : HtmlT genre m (Options genre m) := do
  return (← read).options

def HtmlT.withOptions (opts : Options g m → Options g m) (act : HtmlT g m α) : HtmlT g m α :=
  withReader (fun ctxt => {ctxt with options := opts ctxt.options}) act

def HtmlT.context [Monad m] : HtmlT genre m genre.TraverseContext := do
  return (← read).traverseContext

def HtmlT.state [Monad m] : HtmlT genre m genre.TraverseState := do
  return (← read).traverseState

def HtmlT.definitionIds [Monad m] : HtmlT genre m (Lean.NameMap String) := do
  return (← read).definitionIds

def HtmlT.linkTargets [Monad m] : HtmlT genre m Code.LinkTargets := do
  return (← read).linkTargets

def HtmlT.codeOptions [Monad m] : HtmlT genre m Code.HighlightHtmlM.Options := do
  return (← read).codeOptions


def HtmlT.logError [Monad m] (message : String) : HtmlT genre m Unit := do (← options).logError message

instance [Monad m] : MonadLift HighlightHtmlM (HtmlT genre m) where
  monadLift act := do modifyGet (act ⟨← HtmlT.linkTargets, ← HtmlT.definitionIds, ← HtmlT.codeOptions⟩)

open HtmlT

def mkPartHeader (level : Nat) (contents : Html) (headerAttrs : Array (String × String) := #[]) : Html :=
  .tag s!"h{level}" headerAttrs contents

class ToHtml (genre : Genre) (m : Type → Type) (α : Type u) where
  toHtml (val : α) : HtmlT genre m Html

class GenreHtml (genre : Genre) (m : Type → Type) where
  /--
  Customizable rendering of parts for genres.

  The `partHtml` parameter is a callback to re-invoke HTML generation. Its `mkHeader` parameter
  should create a suitable `h` tag, when provided with a level and contents. The default version
  does only this; customized versions may add HTML `id` attributes, section numbering, etc.

  Instances should not return tags other than `hN` at the provided level, because this custom
  version is used only when the part's metadata is not `none`.
  -/
  part
    (partHtml : Part genre → (mkHeader : Nat → Html → Html := mkPartHeader) → HtmlT genre m Html)
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

partial def Part.toHtml [Monad m] [GenreHtml g m] [TraversePart g]
    (p : Part g) (mkHeader : Nat → Html → Html := mkPartHeader) : HtmlT g m Html :=
  match p.metadata with
  | .none => do
    pure {{
      <section>
        {{ mkHeader (← options).headerLevel (.seq <| ← p.title.mapM ToHtml.toHtml) }}
        {{← p.content.mapM ToHtml.toHtml  }}
        {{← withOptions (fun o => {o with headerLevel := o.headerLevel + 1}) <|
          p.subParts.mapM fun subPart =>
            withReader (fun ctxt => {ctxt with traverseContext := TraversePart.inPart subPart ctxt.traverseContext}) <|
              Part.toHtml (mkHeader := mkPartHeader) subPart }}
      </section>
    }}
  | some m =>
    GenreHtml.part (fun p mkHeader => Part.toHtml p (mkHeader := mkHeader)) m p.withoutMetadata

instance [Monad m] [GenreHtml g m] [TraversePart g] : ToHtml g m (Part g) where
  toHtml p := Part.toHtml p

instance : GenreHtml .none m where
  part _ m := nomatch m
  block _ _ x := nomatch x
  inline _ x := nomatch x

defmethod Genre.toHtml (g : Genre) [ToHtml g m α]
    (options : Options g m) (context : g.TraverseContext) (state : g.TraverseState)
    (definitionIds : Lean.NameMap String)
    (linkTargets : Code.LinkTargets) (codeOptions : Code.HighlightHtmlM.Options)
    (x : α) : StateT (Verso.Code.Hover.State Html) m Html :=
  ToHtml.toHtml x ⟨options, context, state, definitionIds, linkTargets, codeOptions⟩

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
  #eval Genre.none.toHtml (m:=Id) {logError := fun _ => ()} () () {} {} {} e |>.run .empty |>.fst
end

def embody (content : Html) : Html := {{
<html>
<head></head>
<body> {{ content }} </body>
</html>
}}
