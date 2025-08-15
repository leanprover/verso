/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Parser
import Verso.Parser

namespace Verso.Output

open Lean

inductive Html where
  | text (escape : Bool) (string : String)
  | tag (name : String) (attrs : Array (String × String)) (contents : Html)
  | seq (contents : Array Html)
deriving Repr, Inhabited, TypeName, BEq, Hashable

open Syntax in
partial instance : Quote Html where
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

def Html.empty : Html := .seq #[]

def Html.ofString : String → Html := .text true

def Html.append : Html → Html → Html
  | .seq xs, .seq ys => .seq (xs ++ ys)
  | .seq xs, other => .seq (xs.push other)
  | other, .seq ys => .seq (#[other] ++ ys)
  | x, y => .seq #[x, y]

instance : Append Html := ⟨Html.append⟩

def Html.fromArray (htmls : Array Html) : Html :=
  .seq <| htmls.foldl glue .empty
where
  glue
    | arr, .seq hs => arr.append hs
    | arr, other => arr.push other

def Html.fromList (htmls : List Html) : Html := Id.run do
  let mut out := Html.empty
  for elt in htmls do
    out := out ++ elt
  out

instance : Coe (Array Html) Html where
  coe arr := Html.fromArray arr

instance : Coe (List Html) Html where
  coe arr := Html.fromList arr

def revFrom (i : Nat) (input : Array α) (output : Array α := #[]) : Array α :=
  if h : i < input.size then
    revFrom (i+1) input (output.push input[i])
  else output
termination_by input.size - i

namespace Html

def doctype := "<!DOCTYPE html>"

/-- Visit the entire tree, applying rewrites in some monad. Return `none` to signal that no rewrites are to be performed. -/
partial def visitM [Monad m]
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

/-- Void tags are those that cannot have child nodes - they must not have closing tags.

See https://developer.mozilla.org/en-US/docs/Glossary/Void_element
 -/
private def voidTags : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source", "track", "wbr"]

/--
Tags for which tag omission rules do not permit omitting the
closing tag (the XHTML-style `<selfclosing/>` syntax is also invalid
here). This list includes all SVG tags, since SVG is XML based and XML requires
that every tag be explicitly closed.

This was manually constructed by grepping through
- https://html.spec.whatwg.org/
- https://www.w3.org/TR/SVG11/eltindex.html
- https://www.w3.org/TR/SVGTiny12/elementTable.html
- https://www.w3.org/TR/SVG2/eltindex.html
-/
private def mustClose : List String :=
  ["b", "u", "mark", "bdi", "bdo", "span", "ins", "del", "picture", "iframe",
   "object", "video", "audio", "map", "table", "form", "label", "button", "select",
   "datalist", "textarea", "output", "progress", "meter", "fieldset", "legend",
   "details", "summary", "dialog", "script", "noscript", "template", "slot",
   "canvas", "title", "style", "article", "section", "nav", "aside", "h1",
   "h2", "h3", "h4", "h5", "h6", "hgroup", "header", "footer", "address", "pre",
   "blockquote", "ol", "ul", "menu", "dl", "figure", "figcaption", "main", "search",
   "div", "a", "em", "strong", "small", "s", "cite", "q", "dfn", "abbr", "ruby",
   "data", "time", "code", "var", "samp", "kbd", "sub", "sup", "i"] ++
  -- SVG tags begin here
  ["altGlyph", "a", "altGlyphDef", "altGlyphItem", "animate", "animateColor",
   "animateMotion", "animateTransform", "circle", "clipPath", "color-profile",
   "cursor", "defs", "desc", "ellipse", "feBlend", "feColorMatrix",
   "feComponentTransfer", "feComposite", "feConvolveMatrix", "feDiffuseLighting",
   "feDisplacementMap", "feDistantLight", "feFlood", "feFuncA", "feFuncB",
   "feFuncG", "feFuncR", "feGaussianBlur", "feImage", "feMerge", "feMergeNode",
   "feMorphology", "feOffset", "fePointLight", "feSpecularLighting", "feSpotLight",
   "feTile", "feTurbulence", "filter", "font", "font-face", "font-face-format",
   "font-face-name", "font-face-src", "font-face-uri", "foreignObject", "g",
   "glyph", "glyphRef", "hkern", "image", "line", "linearGradient", "marker",
   "mask", "metadata", "missing-glyph", "mpath", "path", "pattern", "polygon",
   "polyline", "radialGradient", "rect", "script", "set", "stop", "style", "svg",
   "switch", "symbol", "text", "textPath", "title", "tref", "tspan", "use", "view",
   "vkern", "audio", "canvas", "discard", "feDropShadow", "iframe", "unknown",
   "video"]

/--
  Tags to break the line after without risking weird results
-/
private def newlineAfter : List String := [
  "p", "div", "li", "ul", "ol", "section", "header", "nav", "head", "body",
  "script", "link", "meta", "html"] ++ [1,2,3,4,5,6].map (s!"h{·}")

open Lean.Parser (rawIdent)

section
def attributeNameKind := `Verso.Output.Html.attributeName

open Lean.Parser
open Verso.Parser
def attributeNameFn : ParserFn :=
  atomicFn <|
    nodeFn attributeNameKind <|
      asStringFn <| andthenFn (satisfyFn versoAttributeNameChar) (manyFn attributeNameCharFn)
where
  -- A slight divergence from the spec for the sake of quasiquotation syntax:
  -- attribute names can't start with a few special characters that the spec allows but that
  -- are very obscure and make parser errors much worse.
  versoAttributeNameChar (c : Char) : Bool := c ∉ ['{', '}', '<', '"', '\''] && attributeNameChar c
  -- https://html.spec.whatwg.org/multipage/syntax.html#attributes-2
  attributeNameChar (c : Char) : Bool :=
    !(isControl c) && c ∉ [' ', '"', '\'', '>', '/', '='] && !(isNonChar c)
  -- https://infra.spec.whatwg.org/#control
  isControl (c : Char) :=
    let n := c.toNat
    n ≥ 0x007f && n ≤ 0x009f
  -- https://infra.spec.whatwg.org/#noncharacter
  isNonChar (c : Char) :=
    let n := c.toNat
    (n ≥ 0xfdd0 && n ≤ 0xfdef) ||
    n ∈ [0xFFFE, 0xFFFF, 0x1FFFE, 0x1FFFF, 0x2FFFE, 0x2FFFF, 0x3FFFE, 0x3FFFF, 0x4FFFE,
      0x4FFFF, 0x5FFFE, 0x5FFFF, 0x6FFFE, 0x6FFFF, 0x7FFFE, 0x7FFFF, 0x8FFFE, 0x8FFFF,
      0x9FFFE, 0x9FFFF, 0xAFFFE, 0xAFFFF, 0xBFFFE, 0xBFFFF, 0xCFFFE, 0xCFFFF, 0xDFFFE,
      0xDFFFF, 0xEFFFE, 0xEFFFF, 0xFFFFE, 0xFFFFF, 0x10FFFE, 0x10FFFF]
  attributeNameCharFn := satisfyFn attributeNameChar "attribute name"


def attributeNameNoAntiquot : Parser where
  fn := andthenFn attributeNameFn (takeWhileFn Char.isWhitespace)

def attributeName : Parser :=
  withAntiquot (mkAntiquot "attributeName" attributeNameKind) attributeNameNoAntiquot

@[combinator_parenthesizer attributeName]
def attributeName.parenthesizer := PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter attributeName]
def attributeName.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

defmethod TSyntax.getAttributeName (stx : TSyntax attributeNameKind) : String :=
  if let ⟨.node _ _ #[.atom _ name]⟩ := stx then
    name
  else panic! "Not an attribute name"

end

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
scoped syntax (name := attrAntiquoted) "{{" term "}}" : attrib

partial def _root_.Lean.TSyntax.tagName : TSyntax `tag_name → String
  | ⟨.node _ _ #[.atom _ x]⟩ => x
  | ⟨.node _ _ #[.ident _ _ x ..]⟩ => x.eraseMacroScopes.toString
  | _ => "fake tag name!!!"


scoped syntax "{{" term "}}" : html
scoped syntax "<" tag_name attrib* ">" html* "</" tag_name ">" : html
scoped syntax "<" tag_name attrib* "/" ">" : html
scoped syntax str : html
scoped syntax "s!" interpolatedStr(term) : html
scoped syntax "r!" str : html

scoped syntax "{{"  html+ "}}" : term
scoped syntax "<<<" (attrib ppSpace) * ">>>" : term

open Lean Elab Term Meta in
def elabAttrs (stxs : Array (TSyntax `attrib)) : TermElabM Expr := do
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
    | `(attrAntiquoted| {{ $e }}) =>
      let e ← elabTermEnsuringType e (← mkAppM ``Array #[attrType])
      attrs ← mkAppM ``Array.append #[attrs, e]
    | _ => withRef stx throwUnsupportedSyntax
  return attrs

open Lean Elab Term Meta in
partial def elabHtml (stx : TSyntax `html) : TermElabM Expr := withRef stx do
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
          let noContents := src.extract start (src.prev stop)
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


scoped instance : Coe String Html := ⟨.text true⟩

def testAttrs := {{ <html charset="UTF-8" charset = "UTF-8" a="b" a-b-c="44" {{#[("x", "y")] }} /> }}

/--
info: Verso.Output.Html.tag
  "html"
  #[("charset", "UTF-8"), ("charset", "UTF-8"), ("a", "b"), ("a-b-c", "44"), ("x", "y")]
  (Verso.Output.Html.seq #[])
-/
#guard_msgs in
#eval testAttrs

def testAttrsAntiquotes :=
  {{ <html charset={{"UTF" ++ "-8"}} "charset" = "UTF-8" a="b" a-b-c="44" {{#[("x", "y")]}} /> }}

/--
info: Verso.Output.Html.tag
  "html"
  #[("charset", "UTF-8"), ("charset", "UTF-8"), ("a", "b"), ("a-b-c", "44"), ("x", "y")]
  (Verso.Output.Html.seq #[])
-/
#guard_msgs in
#eval testAttrsAntiquotes

def test : Html := {{
  <html>
  <head>
    <meta charset="UTF-8"/>
    <script></script>
  </head>
  <body lang="en" class="thing" data-foo="data foo">
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
        (Verso.Output.Html.tag
          "p"
          #[]
          (Verso.Output.Html.seq
            #[Verso.Output.Html.text true "foo bar", Verso.Output.Html.tag "br" #[] (Verso.Output.Html.seq #[]),
              Verso.Output.Html.text true "hey"]))])
-/
#guard_msgs in
  #eval test

def leanKwTest : Html := {{
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
partial def format : Html → Std.Format
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

-- TODO nicely readable HTML output
partial def asString (html : Html) (indent : Nat := 0) (breakLines := true) : String :=
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
  newline i := "\n" ++ String.mk (List.replicate i ' ')
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
    <p>
      foo bar<br>hey</p>
    </body>
  </html>
-/
#guard_msgs in
  #eval IO.println <| "|\n" ++ test.asString
