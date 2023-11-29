import Lean.Data.RBMap

import LeanDoc.Doc
import LeanDoc.Html
import LeanDoc.Doc.Html

import LeanDoc.Genre.Blog
import LeanDoc.Genre.Blog.Site.Syntax

open LeanDoc.Doc (Genre Part)
open LeanDoc.Doc.Html

namespace LeanDoc.Genre


namespace Blog

open LeanDoc.Html
open Lean (RBMap)

section

open Lean Elab
open LeanDoc Doc Elab


@[role_expander label]
def label : RoleExpander
  | #[.anonymous (.name l)], stxs => do
    let args ← stxs.mapM elabInline
    let val ← ``(Inline.other (Blog.InlineExt.label $(quote l.getId)) #[ $[ $args ],* ])
    pure #[val]
  | args, stx =>
    throwError "{repr args} & {stx}"
    --throwUnsupportedSyntax

@[role_expander ref]
def ref : RoleExpander
  | #[.anonymous (.name l)], stxs => do
    let args ← stxs.mapM elabInline
    let val ← ``(Inline.other (Blog.InlineExt.ref $(quote l.getId)) #[ $[ $args ],* ])
    pure #[val]
  | _, _ => throwUnsupportedSyntax


@[role_expander page_link]
def page_link : RoleExpander
  | #[.anonymous (.name page)], stxs => do
    let args ← stxs.mapM elabInline
    let pageName := mkIdentFrom page <| docName page.getId
    let val ← ``(Inline.other (Blog.InlineExt.pageref $(quote pageName.getId)) #[ $[ $args ],* ])
    pure #[val]
  | _, _ => throwUnsupportedSyntax


end

private def filterString (p : Char → Bool) (str : String) : String := Id.run <| do
  let mut out := ""
  for c in str.toList do
    if p c then out := out.push c
  pure out

def blogMain (theme : Theme) (site : Site) (options : List String) : IO UInt32 := do
  let cfg ← opts {} options
  let (site, xref) ← site.traverse cfg
  site.generate theme {site := site, ctxt := ⟨[], cfg⟩, xref := xref, dir := cfg.destination, config := cfg}
  pure 0

where
  opts (cfg : Config)
    | ("--output"::dir::more) => opts {cfg with destination := dir} more
    | ("--drafts"::more) => opts {cfg with showDrafts := true} more
    | (other :: _) => throw (↑ s!"Unknown option {other}")
    | [] => pure cfg

end Blog
namespace Manual

end Manual
