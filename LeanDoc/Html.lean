import Lean
import Std.Tactic.GuardMsgs

namespace LeanDoc

open Lean

inductive Html where
  | text (string : String)
  | tag (name : String) (attrs : Array (String × String)) (contents : Array Html)
deriving Repr, Inhabited

namespace Html

declare_syntax_cat html
declare_syntax_cat tag_name
declare_syntax_cat attrib
declare_syntax_cat attrib_val
scoped syntax str : attrib_val
scoped syntax "{{" term "}}" : attrib_val
scoped syntax ident "=" attrib_val : attrib
scoped syntax "class" "=" attrib_val : attrib

scoped syntax ident : tag_name
scoped syntax "section" : tag_name

partial def _root_.Lean.TSyntax.tagName : TSyntax `tag_name → String
  | ⟨.node _ _ #[.atom _ x]⟩ => x
  | ⟨.node _ _ #[.ident _ _ x ..]⟩ => x.eraseMacroScopes.toString
  | _ => panic! "oops wrong syntax"


scoped syntax "{{" term "}}" : html
scoped syntax "{{" term "}}*" : html
scoped syntax "<" tag_name attrib* ">" html* "</" tag_name ">" : html
scoped syntax  "<" tag_name attrib* "/" ">" : html
scoped syntax str : html

scoped syntax "{{"  html "}}" : term
scoped syntax "{{{" attrib* "}}}" : term

open Lean.Macro in
macro_rules
  | `(term| {{{ $attrs* }}} ) => do
    let attrsOut ← attrs.mapM fun
      | `(attrib| $name:ident = $val:str) => `(term| ($(quote name.getId.toString), $val))
      | `(attrib| $name:ident = {{ $e }} ) => `(term| ($(quote name.getId.toString), $e))
      | `(attrib| class = $val:str) => `(term| ("class", $val))
      | `(attrib| class = {{ $e }}) => `(term| ("class", $e))
      | _ => throwUnsupported
    `(term| #[ $[$attrsOut],* ] )
  | `(term| {{ {{ $e:term }} }} ) => pure e
  | `(term| {{ $s:str }} ) => ``(Html.text $s)
  | `(term| {{ <$tag:tag_name $[$extra]* > {{ $content:term }}* </ $tag':tag_name> }}) => do
    if tag.tagName != tag'.tagName then
      Macro.throwErrorAt tag' s!"Mismatched closing tag, expected {tag.tagName} but got {tag'.tagName}"
    ``(Html.tag $(quote tag.tagName) {{{ $extra* }}} $content)
  | `(term| {{ <$tag:tag_name $[$extra]* > $[$content:html]* </ $tag':tag_name> }}) => do
    if tag.tagName != tag'.tagName then
      Macro.throwErrorAt tag' s!"Mismatched closing tag, expected {tag.tagName} but got {tag'.tagName}"
    ``(Html.tag $(quote tag.tagName) {{{ $extra* }}} #[$[ {{ $content }} ],*] )
  | `(term| {{ <$tag:tag_name $[$extra]* /> }}) => ``(Html.tag $(quote tag.tagName) {{{ $extra* }}} #[] )

scoped instance : Coe String Html := ⟨.text⟩

def test : Html := {{
  <html>
  <body lang="en" class="thing">
  <p> "foo bar" </p>
  </body>
  </html>
}}

/--
info: LeanDoc.Html.tag
  "html"
  #[]
  #[LeanDoc.Html.tag
      "body"
      #[("lang", "en"), ("class", "thing")]
      #[LeanDoc.Html.tag "p" #[] #[LeanDoc.Html.text "foo bar"]]]
-/
#guard_msgs in
  #eval test

open Std.Format in
partial def Html.format : Html → Std.Format
  | .text str => .text (str.replace "<" "&lt;" |>.replace ">" "&gt;")
  | .tag name attrs #[] =>
      Format.group (("<" ++ name) ++ group (line.prefixJoin (attrs.toList.map fun (k, v) => group (k ++ "=" ++ Format.line ++ s!"\"{v}\""))) ++ "/>")
  | .tag "pre" attrs body =>
      Format.group ("<pre" ++ group (line.prefixJoin (attrs.toList.map fun (k, v) => group (k ++ "=" ++ Format.line ++ s!"\"{v}\""))) ++ ">") ++ line ++
      nil.joinSep (body.toList.map Html.format) ++ line ++
      Format.group ("</pre>")
  | .tag name attrs body =>
    .nest 3 (line.joinSep [
      Format.group (("<" ++ name) ++ group (line.prefixJoin (attrs.toList.map fun (k, v) => group (k ++ "=" ++ Format.line ++ s!"\"{v}\""))) ++ ">"),
      Format.group (line.joinSep <| body.toList.map Html.format)
    ]) ++ line ++ Format.group ("</" ++ name ++ ">")

