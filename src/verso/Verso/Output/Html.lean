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

import Verso.Output.Html.Entities
public import Verso.Output.Html.AttributeName
public import Verso.Output.Html.Comments
public meta import Verso.Output.Html.AttributeName
public meta import Verso.Output.Html.Comments
public meta import Verso.Output.Html.Tags
import Verso.Output.Html.Tags

namespace Verso.Output

open Lean

/--
A representation of HTML, used to render Verso to the web.
-/
public inductive Html where
  /--
  Textual content. If `escape` is `true`, then characters such as `'&'` are escaped to entities such
  as `"&amp;"` during rendering.
  -/
  | text (escape : Bool) (string : String)
  /--
  A tag with the given name and attributes.
  -/
  | tag (name : String) (attrs : Array (String × String)) (contents : Html)
  /--
  A sequence of HTML values.
  -/
  | seq (contents : Array Html)
deriving Repr, Inhabited, TypeName, BEq, Hashable

public instance : ToJson Html where
  toJson := private to
where
  to
    | .text true string => .str string
    | .text false string => json%{"raw": $string}
    | .tag name attrs contents =>
      let attrs : Json := .arr <| attrs.map fun (x, y) => json%{"name": $x, "value": $y}
      json%{"tag": $name, "attrs": $attrs, "content": $(to contents)}
    | .seq xs => .arr <| xs.map to

public partial instance : FromJson Html where
  fromJson? := private from?
where
  from?
    | .str s => pure <| .text true s
    | .arr xs => .seq <$> xs.mapM from?
    | json@(.obj o) => do
      if let some name := o["tag"]? then
        let .str name := name
          | throw s!"Expected a string as a tag name, got: {name.compress}"
        let attrs ← json.getObjValAs? (Array Json) "attrs"
        let attrs ← attrs.mapM fun a => do
          return (← a.getObjValAs? String "name", ← a.getObjValAs? String "value")
        let content ← json.getObjVal? "content" >>= from?
        return .tag name attrs content
      else if let some string := o["raw"]? then
        let .str string := string
          | throw s!"Expected a string for raw content, got: {string.compress}"
        return .text false string
      else
        throw <|
          s!"Failed to deserialize {json.compress} as HTML. " ++
          "Expected key \"tag\" or key \"raw\"."
    | other => throw s!"Failed to deserialize {other.compress} as HTML"


open Syntax in
public partial instance : Quote Html where
  quote := q
where
  quoteArray {α : _} (_inst : Quote α) (xs : Array α) : TSyntax `term :=
    mkCApp ``List.toArray #[quote xs.toList]
  q
    | .text esc str =>
      mkCApp ``Html.text #[quote esc, quote str]
    | .tag name attrs contents =>
      mkCApp ``Html.tag #[quote name, quote attrs, q contents]
    | .seq contents =>
      mkCApp ``Html.seq #[quoteArray ⟨q⟩ contents]

/--
The empty HTML document.
-/
@[suggest_for Verso.Output.Html.nil Verso.Output.Html.none]
public def Html.empty : Html := .seq #[]

/--
Converts a string to HTML, escaping special characters.
-/
public def Html.ofString : String → Html := .text true

/--
Appends two HTML documents.
-/
public def Html.append : Html → Html → Html
  | .seq xs, .seq ys => .seq (xs ++ ys)
  | .seq xs, other => .seq (xs.push other)
  | other, .seq ys => .seq (#[other] ++ ys)
  | x, y => .seq #[x, y]

public instance : Append Html := ⟨Html.append⟩

/--
If the HTML consists of a single tag, then the given attribute is set to the provided value. If the
attribute already exists, then its value is replaced.

If the HTML is not a single tag, no changes are made.
-/
public def Html.setAttribute (attr : String) (value : String) (html : Html) : Html :=
  match html with
  | .tag name attrs children =>
    let attrs :=
      if let some i := attrs.findFinIdx? (·.1 == attr) then
        attrs.set i (attr, value)
      else
        attrs.push (attr, value)
    .tag name attrs children
  | _ => html

/--
If the HTML consists of a single tag, then the given attribute is set to the provided value. If the
attribute already exists, then its value is replaced.

Panics if the HTML is not a single tag.
-/
public def Html.setAttribute! (attr : String) (value : String) (html : Html) : Html :=
  match html with
  | .tag .. => html.setAttribute attr value
  | other => panic! s!"Not a single HTML node: {repr other}"


/--
Converts an array of HTML elements into a single element by appending them.

This is equivalent to using `Html.seq`, but may result a more compact representation.
-/
public def Html.fromArray (htmls : Array Html) : Html :=
  .seq <| htmls.foldl glue .empty
where
  glue
    | arr, .seq hs => arr.append hs
    | arr, other => arr.push other

/--
Converts a list of HTML elements into a single element by appending them.

This is equivalent to using `Html.seq` on the corresponding array, but may result in a more compact representation.
-/
public def Html.fromList (htmls : List Html) : Html := Id.run do
  let mut out := Html.empty
  for elt in htmls do
    out := out ++ elt
  out

public instance : Coe (Array Html) Html where
  coe arr := Html.fromArray arr

public instance : Coe (List Html) Html where
  coe arr := Html.fromList arr

private def revFrom (i : Nat) (input : Array α) (output : Array α := #[]) : Array α :=
  if h : i < input.size then
    revFrom (i+1) input (output.push input[i])
  else output
termination_by input.size - i

namespace Html

/-- The default `DOCTYPE` for HTML5. -/
public abbrev doctype := "<!DOCTYPE html>"

/-- Visit the entire tree, applying rewrites in some monad. Return `none` to signal that no rewrites are to be performed. -/
public partial def visitM [Monad m]
    (text : (escape : Bool) → String → m (Option Html) := (fun _ _ => pure none))
    (tag : (name : String) → (attrs : Array (String × String)) → (contents : Html) → m (Option Html) := fun _ _ _ => pure none)
    (seq : Array Html → m (Option Html) := fun _ => pure none)
    (html : Html) : m Html :=
  match html with
  | .text esc str => do pure <| (← text esc str).getD html
  | .tag name attrs contents => do
    let contents' ← contents.visitM (text := text) (tag := tag) (seq := seq)
    pure <| (← tag name attrs contents').getD (.tag name attrs contents')
  | .seq elts => do
    let elts' ← elts.mapM (visitM (text := text) (tag := tag) (seq := seq))
    pure <| (← seq elts').getD (.seq elts')

public section

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

public meta partial def _root_.Lean.TSyntax.tagName : TSyntax `tag_name → String
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
end

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
    return (← mkAppM ``Html.empty #[])
  match stx with
  | `(html| {{ $e:term }} ) =>
    elabTermEnsuringType e (some (.const ``Html []))
  | `(html| $text:str ) =>
    mkAppM ``Html.text #[toExpr true, toExpr text.getString]
  | `(html| s! $txt:interpolatedStr ) => do
    let txt ← elabTermEnsuringType (← `(s!$txt:interpolatedStr)) (some <| .const ``String [])
    mkAppM ``Html.text #[toExpr true, txt]
  | `(html| r! $txt:str ) =>
    mkAppM ``Html.text #[toExpr false, toExpr txt.getString]
  | `(html| <%$tk $tag:tag_name $[$extra]* >%$tk' $[$content:html]* </ $tag':tag_name>) => do
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
    let content ←
      if h : content.size = 1 then
        elabHtml content[0]
      else
        let content ← content.mapM elabHtml
        let content ← mkArrayLit (.const ``Html []) content.toList
        mkAppM ``Html.fromArray #[content]
    mkAppM ``Html.tag #[toExpr tag.tagName, attrs, content]
  | `(html| <$tag:tag_name $[$extra]* />) =>
    let attrs ← elabAttrs extra
    mkAppM ``Html.tag #[toExpr tag.tagName, attrs, ← mkAppM ``Html.empty #[]]
  | _ => throwUnsupportedSyntax

elab_rules : term
  | `(term| {{ $h:html }}) =>
    withRef h <| elabHtml h
  | `(term| {{ $[$h:html]* }}) => do
    let h ← h.mapM fun (x : TSyntax `html) => withRef x <| elabHtml x
    Meta.mkAppM ``Html.fromArray #[← Meta.mkArrayLit (.const ``Html []) h.toList]


public scoped instance : Coe String Html := ⟨.text true⟩

private def testAttrs := {{ <html charset="UTF-8" charset = "UTF-8" a="b" a-b-c="44" {{#[("x", "y")] }} /> }}

/--
info: Verso.Output.Html.tag
  "html"
  #[("charset", "UTF-8"), ("charset", "UTF-8"), ("a", "b"), ("a-b-c", "44"), ("x", "y")]
  (Verso.Output.Html.seq #[])
-/
#guard_msgs in
#eval testAttrs

private def testAttrsAntiquotes :=
  {{ <html charset={{"UTF" ++ "-8"}} "charset" = "UTF-8" a="b" a-b-c="44" {{#[("x", "y")]}} /> }}

/--
info: Verso.Output.Html.tag
  "html"
  #[("charset", "UTF-8"), ("charset", "UTF-8"), ("a", "b"), ("a-b-c", "44"), ("x", "y")]
  (Verso.Output.Html.seq #[])
-/
#guard_msgs in
#eval testAttrsAntiquotes

private def test : Html := {{
  <html>
  <head>
    <!-- Set the contents -->
    <meta charset="UTF-8"/>
    <script></script>
  </head>
  <body lang="en" class="thing" data-foo="data foo">
  <input type="checkbox" checked />
  <p> "foo bar" <br/> "hey" </p>
  </body>
  </html>
}}

/--
info: Verso.Output.Html.tag
  "html"
  #[]
  (Verso.Output.Html.seq
    #[Verso.Output.Html.tag
        "head"
        #[]
        (Verso.Output.Html.seq
          #[Verso.Output.Html.tag "meta" #[("charset", "UTF-8")] (Verso.Output.Html.seq #[]),
            Verso.Output.Html.tag "script" #[] (Verso.Output.Html.seq #[])]),
      Verso.Output.Html.tag
        "body"
        #[("lang", "en"), ("class", "thing"), ("data-foo", "data foo")]
        (Verso.Output.Html.seq
          #[Verso.Output.Html.tag "input" #[("type", "checkbox"), ("checked", "")] (Verso.Output.Html.seq #[]),
            Verso.Output.Html.tag
              "p"
              #[]
              (Verso.Output.Html.seq
                #[Verso.Output.Html.text true "foo bar", Verso.Output.Html.tag "br" #[] (Verso.Output.Html.seq #[]),
                  Verso.Output.Html.text true "hey"])])])
-/
#guard_msgs in
  #eval test

private def leanKwTest : Html := {{
  <label for="foo">"Blah"</label>
}}

/-- info: Verso.Output.Html.tag "label" #[("for", "foo")] (Verso.Output.Html.text true "Blah") -/
#guard_msgs in
  #eval leanKwTest


/--
error: `<br>` doesn't allow contents

Hint: Remove contents
  <̵b̵r̵>̵"̵f̵o̵o̵"̵ ̵"̵f̵o̵o̵"̵<̵/̵b̵r̵>̵<̲b̲r̲/̲>̲
-/
#guard_msgs in
  #eval show Html from {{ <br>"foo" "foo"</br> }}

open Std.Format in

/--
Converts HTML into a pretty-printer document. This is useful for debugging, but it does not preserve
whitespace around preformatted content and scripts.
-/
public partial def format : Html → Std.Format
  | .text true str => .text (str.replace "<" "&lt;" |>.replace ">" "&gt;")
  | .text false str => .text str
  | .tag name attrs (.seq #[]) =>
      Format.group (("<" ++ name) ++ group (line.prefixJoin (attrs.toList.map fun (k, v) => group (k ++ "=" ++ Format.line ++ s!"\"{v}\""))) ++ "/>")
  | .tag "pre" attrs body =>
      Format.group ("<pre" ++ group (line.prefixJoin (attrs.toList.map fun (k, v) => group (k ++ "=" ++ Format.line ++ s!"\"{v}\""))) ++ ">") ++ line ++
      Html.format body ++ line ++
      Format.group ("</pre>")
  | .tag name attrs body =>
    .nest 3 (line.joinSep [
      Format.group (("<" ++ name) ++ group (line.prefixJoin (attrs.toList.map fun (k, v) => group (k ++ "=" ++ Format.line ++ s!"\"{v}\""))) ++ ">"),
      Format.group (Html.format body)
    ]) ++ line ++ Format.group ("</" ++ name ++ ">")
  | .seq arr => line.joinSep <| arr.toList.map Html.format

/--
Converts HTML into a string that's suitable for sending to browsers, but is also readable.
-/
public partial def asString (html : Html) (indent : Nat := 0) (breakLines := true) : String :=
  match html with
  | .text true str => str.replace "<" "&lt;" |>.replace ">" "&gt;"
  | .text false str => str
  | .tag "pre" attrs body =>
    "<pre" ++ attrsAsString attrs ++ ">" ++
    Html.asString (indent := 0) (breakLines := false) body ++
    "</pre>" ++ breakline "pre"
  | .tag "code" attrs body =>
    "<code" ++ attrsAsString attrs ++ ">" ++
    Html.asString (indent := 0) (breakLines := false) body ++
    "</code>" ++ breakline "code"
  | .tag name attrs (.seq #[]) =>
    if name ∈ mustClose then
      "<" ++ name ++ attrsAsString attrs ++ "></" ++ name ++ ">" ++ breakline name
    else
      "<" ++ name ++ attrsAsString attrs ++ ">" ++ breakline name
  | .tag name attrs (.seq #[subElem]) =>
    "<" ++ name ++ attrsAsString attrs ++ ">" ++ breakline' name ++
    asString subElem (indent := indent + 2) (breakLines := breakLines) ++
    s!"</{name}>" ++ breakline name
  | .tag name attrs body =>
      "<" ++ name ++ attrsAsString attrs ++ ">" ++ breakline' name ++
      Html.asString body (indent := indent + 2) (breakLines := breakLines) ++
      s!"</{name}>" ++ breakline name
  | .seq elts => String.join (elts.toList.map (Html.asString · (indent := indent) (breakLines := breakLines)))
where
  newline i := "\n" ++ String.ofList (List.replicate i ' ')
  breakline tag := if breakLines && tag ∈ newlineAfter then newline indent else ""
  breakline' tag := if breakLines && tag ∈ newlineAfter then newline (indent + 2) else ""
  attrsAsString xs := String.join <| xs.toList.map (fun ⟨k, v⟩ => s!" {k}=\"{escapeAttr v}\"")
  escapeAttr str := str |>.replace "&" "&amp;" |>.replace "\"" "&quot;"

/--
info: |
<html>
  <head>
    <meta charset="UTF-8">
    <script></script>
    </head>
  <body lang="en" class="thing" data-foo="data foo">
    <input type="checkbox" checked=""><p>
      foo bar<br>hey</p>
    </body>
  </html>
-/
#guard_msgs in
  #eval IO.println <| "|\n" ++ test.asString
