/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean

namespace Verso.Output

open Lean

inductive Html where
  | text (escape : Bool) (string : String)
  | tag (name : String) (attrs : Array (String × String)) (contents : Html)
  | seq (contents : Array Html)
deriving Repr, Inhabited, TypeName

def Html.empty : Html := .seq #[]

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
here)

This was manually constructed by grepping through https://html.spec.whatwg.org/
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
   "data", "time", "code", "var", "samp", "kbd", "sub", "sup", "i"]

/--
  Tags to break the line after without risking weird results
-/
private def newlineAfter : List String := [
  "p", "div", "li", "ul", "ol", "section", "header", "nav", "head", "body",
  "script", "link", "meta", "html"] ++ [1,2,3,4,5,6].map (s!"h{·}")

declare_syntax_cat tag_name
scoped syntax ident : tag_name
scoped syntax "section" : tag_name

declare_syntax_cat html
declare_syntax_cat attrib
declare_syntax_cat attrib_val
scoped syntax str : attrib_val
scoped syntax "s!" interpolatedStr(term) : attrib_val
scoped syntax "{{" term "}}" : attrib_val
scoped syntax ident "=" attrib_val : attrib
scoped syntax str "=" attrib_val : attrib
scoped syntax "class" "=" attrib_val : attrib
scoped syntax "{{" term "}}" : attrib

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
scoped syntax "{{{" attrib* "}}}" : term

open Lean.Macro in
macro_rules
  | `(term| {{{ $attrs* }}} ) => do
    let attrsOut ← attrs.mapM fun
      | `(attrib| $name:ident = $val:str) => `(term| #[($(quote name.getId.toString), $val)])
      | `(attrib| $name:ident = s!$val:interpolatedStr) => `(term| #[($(quote name.getId.toString), s!$val)])
      | `(attrib| $name:ident = {{ $e }} ) => `(term| #[($(quote name.getId.toString), ($e : String))])
      | `(attrib| $name:str = {{ $e }} ) => `(term| #[($(quote name.getString), ($e : String))])
      | `(attrib| class = $val:str) => `(term| #[("class", $val)])
      | `(attrib| class = s!$val:interpolatedStr) => `(term| #[("class", s!$val)])
      | `(attrib| class = {{ $e }}) => `(term| #[("class", ($e : String))])
      | `(attrib| {{ $e }}) => `(term| ($e : Array (String × String)))
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
    ``(Html.tag $(quote tag.tagName) {{{ $extra* }}} {{ $content }} )
  | `(term| {{ <$tag:tag_name $[$extra]* > $[$content:html]* </ $tag':tag_name> }}) => do
    if tag.tagName != tag'.tagName then
      Macro.throwErrorAt tag' s!"Mismatched closing tag, expected {tag.tagName} but got {tag'.tagName}"
    if tag.tagName ∈ voidTags && content.size != 0 then
      Macro.throwErrorAt tag s!"'{tag.tagName}' doesn't allow contents"
    ``(Html.tag $(quote tag.tagName) {{{ $extra* }}} <| Html.fromArray #[$[ ({{ $content }} : Html) ],*] )
  | `(term| {{ <$tag:tag_name $[$extra]* /> }}) => ``(Html.tag $(quote tag.tagName) {{{ $extra* }}} Html.empty )

scoped instance : Coe String Html := ⟨.text true⟩

def test : Html := {{
  <html>
  <head>
    <meta charset="UTF-8"/>
    <script></script>
  </head>
  <body lang="en" class="thing">
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
        #[("lang", "en"), ("class", "thing")]
        (Verso.Output.Html.tag
          "p"
          #[]
          (Verso.Output.Html.seq
            #[Verso.Output.Html.text true "foo bar", Verso.Output.Html.tag "br" #[] (Verso.Output.Html.seq #[]),
              Verso.Output.Html.text true "hey"]))])
-/
#guard_msgs in
  #eval test

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
    "</pre>" ++ newline indent
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
  <body lang="en" class="thing">
    <p>
      foo bar<br>hey</p>
    </body>
  </html>
-/
#guard_msgs in
  #eval IO.println <| "|\n" ++ test.asString
