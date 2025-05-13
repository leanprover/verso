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

open Lean.Macro in
macro_rules
  | `(term| <<< $attrs* >>> ) => do
    let attrsOut ← attrs.mapM fun
      | `(attrib| $name:attributeName = $val:str) => `(term| #[($(quote name.getAttributeName), $val)])
      | `(attrib| $name:attributeName = s!$val:interpolatedStr) => `(term| #[($(quote name.getAttributeName), s!$val)])
      | `(attrib| $name:attributeName = {{ $e }} ) => `(term| #[($(quote name.getAttributeName), ($e : String))])
      | `(attrStrNamed| $name:str = $val:str) => `(term| #[($(quote name.getString), $val)])
      | `(attrStrNamed| $name:str = s!$val:interpolatedStr) => `(term| #[($(quote name.getString), s!$val)])
      | `(attrStrNamed| $name:str = {{ $e }} ) => `(term| #[($(quote name.getString), ($e : String))])
      | `(attrAntiquoted| {{ $e }}) => `(term| ($e : Array (String × String)))
      | _ => throwUnsupported
    `(term| #[ $[($attrsOut : Array (String × String))],* ].foldr (· ++ ·) #[] )
  | `(term| {{ {{ $e:term }} }} ) => ``(($e : Html))
  | `(term| {{ $text:str }} ) => ``(Html.text true $text)
  | `(term| {{ s! $txt:interpolatedStr }} ) => ``(Html.text true s!$txt)
  | `(term| {{ r! $txt:str }} ) => ``(Html.text false $txt)
  | `(term| {{ $html1:html $html2:html $htmls:html*}}) =>
    `({{$html1}} ++ {{$html2}} ++ Html.seq #[$[({{$htmls}} : Html)],*])
  | `(term| {{ <$tag:tag_name $[$extra]* > $content:html </ $tag':tag_name> }}) => do
    if tag.tagName != tag'.tagName then
      Macro.throwErrorAt tag' s!"Mismatched closing tag, expected {tag.tagName} but got {tag'.tagName}"
    if tag.tagName ∈ voidTags then
      Macro.throwErrorAt tag s!"'{tag.tagName}' doesn't allow contents"
    ``(Html.tag $(quote tag.tagName) <<< $extra* >>> {{ $content }} )
  | `(term| {{ <$tag:tag_name $[$extra]* > $[$content:html]* </ $tag':tag_name> }}) => do
    if tag.tagName != tag'.tagName then
      Macro.throwErrorAt tag' s!"Mismatched closing tag, expected {tag.tagName} but got {tag'.tagName}"
    if tag.tagName ∈ voidTags && content.size != 0 then
      Macro.throwErrorAt tag s!"'{tag.tagName}' doesn't allow contents"
    ``(Html.tag $(quote tag.tagName) <<< $extra* >>> <| Html.fromArray #[$[ ({{ $content }} : Html) ],*] )
  | `(term| {{ <$tag:tag_name $[$extra]* /> }}) => ``(Html.tag $(quote tag.tagName) <<< $extra* >>> Html.empty )

scoped instance : Coe String Html := ⟨.text true⟩

def testAttrs := <<< charset="UTF-8" charset = "UTF-8" a="b" a-b-c="44" {{#[("x", "y")]}} >>>

/-- info: #[("charset", "UTF-8"), ("charset", "UTF-8"), ("a", "b"), ("a-b-c", "44"), ("x", "y")] -/
#guard_msgs in
#eval testAttrs

def testAttrsAntiquotes :=
  <<< charset={{"UTF" ++ "-8"}} "charset" = "UTF-8" a="b" a-b-c="44" {{#[("x", "y")]}} >>>

/-- info: #[("charset", "UTF-8"), ("charset", "UTF-8"), ("a", "b"), ("a-b-c", "44"), ("x", "y")] -/
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


/-- error: 'br' doesn't allow contents -/
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
  attrsAsString xs := String.join <| xs.toList.map (fun ⟨k, v⟩ => s!" {k}=\"{v}\"")

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
