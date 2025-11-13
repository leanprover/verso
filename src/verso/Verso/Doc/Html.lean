/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso.Doc
import Verso.Output.Html
import Verso.Method
public import Verso.Code.Highlighted

namespace Verso.Doc.Html

open Verso Output Doc Html
open Verso.Code (HighlightHtmlM)

public structure Options  (m : Type → Type) where
  /-- The level of the top-level headers -/
  headerLevel : Nat := 1
  logError : String → m Unit

public def Options.reinterpret (lift : {α : _} → m α → m' α) (opts : Options m) : Options m' :=
  {opts with
    logError := fun msg => lift <| opts.logError msg}

public def Options.lift [MonadLiftT m m'] (opts : Options m) : Options m' :=
  opts.reinterpret MonadLiftT.monadLift

public structure HtmlT.Context (genre : Genre) (m : Type → Type) where
  options : Options m
  traverseContext : genre.TraverseContext
  traverseState : genre.TraverseState
  /--
  If this name is defined while rendering this HTML, what ID should be placed on the defining
  occurrence for later cross-referencing?
  -/
  definitionIds : Lean.NameMap String
  linkTargets : Code.LinkTargets genre.TraverseContext
  codeOptions : Code.HighlightHtmlM.Options

public def HtmlT.Context.reinterpret (lift : {α : _} → m α → m' α) (ctx : HtmlT.Context g m) : HtmlT.Context g m' :=
  {ctx with
    options := ctx.options.reinterpret lift}

public def HtmlT.Context.lift [MonadLiftT m m'] (ctx : HtmlT.Context g m) : HtmlT.Context g m' :=
  ctx.reinterpret monadLift

public def HtmlT.Context.cast {g1 g2 : Genre}
    (ctx : HtmlT.Context g1 m)
    (context_eq : g1.TraverseContext = g2.TraverseContext := by trivial)
    (state_eq : g1.TraverseState = g2.TraverseState := by trivial) : HtmlT.Context g2 m :=
  { ctx with
    traverseContext := context_eq ▸ ctx.traverseContext,
    traverseState := state_eq ▸ ctx.traverseState,
    linkTargets := context_eq ▸ ctx.linkTargets }

public abbrev HtmlT (genre : Genre) (m : Type → Type) : Type → Type :=
  ReaderT (HtmlT.Context genre m) (StateT (Verso.Code.Hover.State Html) m)

public def HtmlT.cast {g1 g2 : Genre} (act : HtmlT g1 m α)
    (context_eq : g1.TraverseContext = g2.TraverseContext := by trivial)
    (state_eq : g1.TraverseState = g2.TraverseState := by trivial) :
    HtmlT g2 m α :=
  fun ρ σ =>
    act (ρ.cast context_eq.symm state_eq.symm) σ

public def HtmlT.options [Monad m] : HtmlT genre m (Options m) := do
  return (← read).options

public def HtmlT.withOptions (opts : Options m → Options m) (act : HtmlT g m α) : HtmlT g m α :=
  withReader (fun ctxt => {ctxt with options := opts ctxt.options}) act

public def HtmlT.context [Monad m] : HtmlT genre m genre.TraverseContext := do
  return (← read).traverseContext

public def HtmlT.state [Monad m] : HtmlT genre m genre.TraverseState := do
  return (← read).traverseState

public def HtmlT.definitionIds [Monad m] : HtmlT genre m (Lean.NameMap String) := do
  return (← read).definitionIds

public def HtmlT.linkTargets [Monad m] : HtmlT genre m (Code.LinkTargets genre.TraverseContext) := do
  return (← read).linkTargets

public def HtmlT.codeOptions [Monad m] : HtmlT genre m Code.HighlightHtmlM.Options := do
  return (← read).codeOptions

public def HtmlT.logError [Monad m] (message : String) : HtmlT genre m Unit := do (← options).logError message

public instance [Monad m] : MonadLift (HighlightHtmlM genre) (HtmlT genre m) where
  monadLift act := do modifyGet (act ⟨← HtmlT.linkTargets, ← HtmlT.context, ← HtmlT.definitionIds, ← HtmlT.codeOptions⟩)

open HtmlT

public def mkPartHeader (level : Nat) (contents : Html) (headerAttrs : Array (String × String) := #[]) : Html :=
  .tag s!"h{level}" headerAttrs contents

public class ToHtml (genre : Genre) (m : Type → Type) (α : Type u) where
  toHtml (val : α) : HtmlT genre m Html

public class GenreHtml (genre : Genre) (m : Type → Type) where
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

public instance [Monad m] [GenreHtml g m] : ToHtml g m (Inline g) where
  toHtml := private Inline.toHtml

partial def Block.toHtml [Monad m] [GenreHtml g m] [TraverseBlock g] (b : Block g) : HtmlT g m Html :=
  withReader (fun ctxt => { ctxt with traverseContext := TraverseBlock.inBlock b ctxt.traverseContext } ) do
  match b with
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

public instance [Monad m] [GenreHtml g m] [TraverseBlock g] : ToHtml g m (Block g) where
  toHtml := private Block.toHtml

partial def Part.toHtml [Monad m] [GenreHtml g m] [TraversePart g] [TraverseBlock g]
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

public instance [Monad m] [GenreHtml g m] [TraversePart g] [TraverseBlock g] : ToHtml g m (Part g) where
  toHtml p := private Part.toHtml p

public instance : GenreHtml .none m where
  part _ m := nomatch m
  block _ _ x := nomatch x
  inline _ x := nomatch x

public defmethod Genre.toHtml (g : Genre) [ToHtml g m α]
    (options : Options m) (context : g.TraverseContext) (state : g.TraverseState)
    (definitionIds : Lean.NameMap String)
    (linkTargets : Code.LinkTargets g.TraverseContext) (codeOptions : Code.HighlightHtmlM.Options)
    (x : α) : StateT (Verso.Code.Hover.State Html) m Html :=
  ToHtml.toHtml x ⟨options, context, state, definitionIds, linkTargets, codeOptions⟩
