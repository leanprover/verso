/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lean.DocString.Parser
public import Lean.Parser.Types
import Lean.Parser
public import Lean.PrettyPrinter.Formatter
public import Lean.PrettyPrinter.Parenthesizer
public import Lean.Elab.Term.TermElabM
meta import Lean.Elab.Term.TermElabM
public meta import Lean.Meta.Hint
public import Lean.Data.Html

import Verso.Output.Html.Entities
public import Verso.Output.Html.AttributeName
public import Verso.Output.Html.Comments
public meta import Verso.Output.Html.AttributeName
public meta import Verso.Output.Html.Comments
public meta import Verso.Output.Html.Tags
import Verso.Output.Html.Tags

/-! ## Additions to the Lean namespace -/

namespace Lean.Html

/--
If the HTML consists of a single tag, then the given attribute is set to the provided value. If the
attribute already exists, then its value is replaced.

If the HTML is not a single tag, no changes are made.
-/
public def setAttribute (attr : String) (value : String) (html : Html) : Html :=
  match html with
  | .element name attrs children =>
    let attrs :=
      if let some i := attrs.findFinIdx? (·.1 == attr) then
        attrs.set i (attr, value)
      else
        attrs.push (attr, value)
    .element name attrs children
  | _ => html

/--
If the HTML consists of a single tag, then the given attribute is set to the provided value. If the
attribute already exists, then its value is replaced.

Panics if the HTML is not a single tag.
-/
public def setAttribute! (attr : String) (value : String) (html : Html) : Html :=
  match html with
  | .element .. => html.setAttribute attr value
  | other => panic! s!"Not a single HTML node: {repr other}"

/--
Wrap content in a named group whose visible label should not participate in the document heading
outline.

Use this for labels that name a grouped region for assistive technology, but are not section
headings. The label is rendered as a paragraph and connected to the group with `aria-labelledby`.
-/
public def labeledGroup
    (groupClass labelClass id label : String)
    (contents : Html) : Html :=
  let groupAttrs :=
    (if groupClass.isEmpty then #[] else #[("class", groupClass)]) ++
      #[("role", "group"), ("aria-labelledby", id)]
  let labelAttrs :=
    (if labelClass.isEmpty then #[] else #[("class", labelClass)]) ++
      #[("id", id)]
  .element "div" groupAttrs <|
    .seq #[
      .element "p" labelAttrs (.text label),
      contents
    ]

end Lean.Html

/-! ## Django/Handlebars-like syntax -/

namespace Verso.Output.Html
open Lean

declare_syntax_cat tag_name
scoped syntax rawIdent : tag_name

declare_syntax_cat html
declare_syntax_cat attrib
declare_syntax_cat attrib_val
scoped syntax (name := attrib_val_str) str : attrib_val
scoped syntax (name := attrib_val_str_interp) "s!" interpolatedStr(term) : attrib_val
scoped syntax (name := attrib_val_antiquote) "{{" term "}}" : attrib_val
scoped syntax (name := attrStrNamed) str " = " attrib_val : attrib
scoped syntax (name := attrRawNamed) attributeName " = " attrib_val : attrib
scoped syntax (name := attrBool) attributeName : attrib
scoped syntax (name := attrAntiquoted) "{{" term "}}" : attrib

public meta def _root_.Lean.TSyntax.tagName : TSyntax `tag_name → String
  | ⟨.node _ _ #[.atom _ x]⟩ => x
  | ⟨.node _ _ #[.ident _ _ x ..]⟩ => x.eraseMacroScopes.toString
  | _ => "unknown"

scoped syntax "{{" term "}}" : html
scoped syntax "<" tag_name attrib* ">" html* "</" tag_name ">" : html
scoped syntax "<" tag_name attrib* "/" ">" : html
scoped syntax (name := comment) "<!--" htmlCommentContents : html
scoped syntax str : html
scoped syntax "s!" interpolatedStr(term) : html
scoped syntax "r!" str : html

scoped syntax "{{"  html+ "}}" : term
scoped syntax "<<<" (attrib ppSpace) * ">>>" : term

open Lean Elab Term Meta in
meta def elabAttrs (stxs : Array (TSyntax `attrib)) : TermElabM Expr := do
  let attrType ← mkAppM ``Prod #[.const ``String [], .const ``String []]
  let mut attrs : Expr ← mkArrayLit attrType []
  for stx in stxs do
    match stx with
    | `(attrib| $name:attributeName = $val:str) =>
      attrs ← mkAppM ``Array.push #[attrs, ← mkAppM ``Prod.mk #[toExpr name.getAttributeName, toExpr val.getString]]
    | `(attrib| $name:attributeName = s!$val:interpolatedStr) =>
      let val ← withRef val <| elabTermEnsuringType (← ``(s!$val:interpolatedStr)) (some (.const ``String []))
      attrs ← mkAppM ``Array.push #[attrs, ← mkAppM ``Prod.mk #[toExpr name.getAttributeName, val]]
    | `(attrib| $name:attributeName = {{ $e }} ) =>
      let val ← withRef e <| elabTermEnsuringType e (some (.const ``String []))
      attrs ← mkAppM ``Array.push #[attrs, ← mkAppM ``Prod.mk #[toExpr name.getAttributeName, val]]
    | `(attrStrNamed| $name:str = $val:str) =>
      attrs ← mkAppM ``Array.push #[attrs, ← mkAppM ``Prod.mk #[toExpr name.getString, toExpr val.getString]]
    | `(attrStrNamed| $name:str = s!$val:interpolatedStr) =>
      let val ← withRef val <| elabTermEnsuringType (← ``(s!$val:interpolatedStr)) (some (.const ``String []))
      attrs ← mkAppM ``Array.push #[attrs, ← mkAppM ``Prod.mk #[toExpr name.getString, val]]
    | `(attrStrNamed| $name:str = {{ $e }} ) =>
      let val ← withRef e <| elabTermEnsuringType e (some (.const ``String []))
      attrs ← mkAppM ``Array.push #[attrs, ← mkAppM ``Prod.mk #[toExpr name.getString, val]]
    | `(attrBool| $name ) =>
      attrs ← mkAppM ``Array.push #[attrs, ← mkAppM ``Prod.mk #[toExpr name.getAttributeName, toExpr ""]]
    | `(attrAntiquoted| {{ $e }}) =>
      let e ← elabTermEnsuringType e (← mkAppM ``Array #[attrType])
      attrs ← mkAppM ``Array.append #[attrs, e]
    | _ => withRef stx throwUnsupportedSyntax
  return attrs

open Lean Elab Term Meta in
meta partial def elabHtml (stx : TSyntax `html) : TermElabM Expr := withRef stx do
  if stx.raw.getKind == ``comment then
    return .const ``Html.empty []
  match stx with
  | `(html| {{ $e:term }} ) =>
    elabTermEnsuringType e (some (.const ``Html []))
  | `(html| $text:str ) =>
    return mkApp (.const ``Html.text []) (toExpr text.getString)
  | `(html| s! $txt:interpolatedStr ) => do
    let txt ← elabTermEnsuringType (← `(s!$txt:interpolatedStr)) (some <| .const ``String [])
    return mkApp (.const ``Html.text []) txt
  | `(html| r! $txt:str ) =>
    return mkApp (.const ``Html.raw []) (toExpr txt.getString)
  | `(html| <%$tk $tag:tag_name $[$extra]* >%$tk' $[$children:html]* </ $tag':tag_name>) => do
    if tag.tagName != tag'.tagName then
      let hint ← MessageData.hint m!"Replace with opening tag" #[tag.tagName] (ref? := some tag')
      throwErrorAt tag' m!"Mismatched closing tag, expected `{tag.tagName}` but got `{tag'.tagName}`\n{hint}"
    if tag.tagName ∈ voidTags then
      let hint ←
        if let some ⟨start, stop⟩ := mkNullNode #[tk, tk'] |>.getRange? then
          let src := (← getFileMap).source
          let noContents := start.extract src (stop.prev src)
          MessageData.hint m!"Remove contents" #[noContents ++ "/>"]
        else pure m!""
      throwErrorAt tag m!"`<{tag.tagName}>` doesn't allow contents{hint}"
    let attrs ← elabAttrs extra
    let children ←
      if h : children.size = 1 then
        elabHtml children[0]
      else
        let children ← children.mapM elabHtml
        let children ← mkArrayLit (.const ``Html []) children.toList
        pure <| mkApp (.const ``Html.ofArray []) children
    return mkApp3 (.const ``Html.element []) (toExpr tag.tagName) attrs children
  | `(html| <$tag:tag_name $[$extra]* />) =>
    let attrs ← elabAttrs extra
    return mkApp3 (.const ``Html.element []) (toExpr tag.tagName) attrs (.const ``Html.empty [])
  | _ => throwUnsupportedSyntax

elab_rules : term
  | `(term| {{ $h:html }}) =>
    withRef h <| elabHtml h
  | `(term| {{ $[$h:html]* }}) => do
    let h ← h.mapM fun (x : TSyntax `html) => withRef x <| elabHtml x
    return h.foldl (init := (.const ``Html.empty [])) (mkApp2 (.const ``Html.append []))

/-- The default `DOCTYPE` for HTML5. -/
public abbrev doctype := "<!DOCTYPE html>"

end Verso.Output.Html

/-! ## Deprecation aliases -/

namespace Verso.Output

-- Constants with same name and type are re-exported in the old namespace.
export Lean (Html Html.seq Html.empty Html.append Html.setAttribute Html.setAttribute!
  Html.labeledGroup)

-- Constants whose name or type changed become deprecated protected abbrevs in the old namespace.
namespace Html

@[deprecated Lean.Html.ofString (since := "2026-09-02")]
protected abbrev text : Bool → String → Html := Lean.Html.ofString

@[deprecated Lean.Html.element (since := "2026-09-02")]
protected abbrev tag : String → Array (String × String) → Html → Html := Lean.Html.element

@[deprecated Lean.Html.text (since := "2026-09-02")]
protected abbrev ofString : String → Html := Lean.Html.text

@[deprecated Lean.Html.ofArray (since := "2026-09-02")]
protected abbrev fromArray : Array Html → Html := Lean.Html.ofArray

@[deprecated Lean.Html.ofList (since := "2026-09-02")]
protected abbrev fromList : List Html → Html := Lean.Html.ofList

@[deprecated Lean.Html.rewritePostM +typeChanged (since := "2026-09-02")]
protected abbrev visitM [Monad m]
    (text : (escape : Bool) → String → m (Option Html) := (fun _ _ => pure none))
    (tag : (name : String) → (attrs : Array (String × String)) → (contents : Html) → m (Option Html) := fun _ _ _ => pure none)
    (seq : Array Html → m (Option Html) := fun _ => pure none)
    (html : Html) : m Html :=
  html.rewritePostM fun h => match h with
    | .text s => return (← text true s).getD h
    | .raw s => return (← text false s).getD h
    | .element t a c => return (← tag t a c).getD h
    | .seq a => return (← seq a).getD h

set_option linter.unusedVariables false in
@[deprecated Lean.Html.render +typeChanged (since := "2026-09-02")]
protected abbrev asString (html : Html) (indent : Nat := 0) (breakLines := true) : String :=
  html.render

end Verso.Output.Html

-- Constants whose name or type changed, and which are commonly used with dot notation,
-- also get a deprecated alias in the new namespace.
namespace Lean.Html

@[deprecated Lean.Html.rewritePostM +typeChanged (since := "2026-09-02")]
public abbrev visitM [Monad m]
    (text : (escape : Bool) → String → m (Option Html) := (fun _ _ => pure none))
    (tag : (name : String) → (attrs : Array (String × String)) → (contents : Html) → m (Option Html) := fun _ _ _ => pure none)
    (seq : Array Html → m (Option Html) := fun _ => pure none)
    (html : Html) : m Html :=
  html.rewritePostM fun h => match h with
    | .text s => return (← text true s).getD h
    | .raw s => return (← text false s).getD h
    | .element t a c => return (← tag t a c).getD h
    | .seq a => return (← seq a).getD h

set_option linter.unusedVariables false in
@[deprecated Lean.Html.render +typeChanged (since := "2026-09-02")]
public abbrev asString (html : Html) (indent : Nat := 0) (breakLines := true) : String :=
  html.render

end Lean.Html
