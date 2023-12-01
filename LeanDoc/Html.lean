/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean
import Std.Tactic.GuardMsgs

namespace LeanDoc

open Lean

inductive Html where
  | text (string : String)
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

instance : Coe (Array Html) Html where
  coe arr := Html.fromArray arr


def revFrom (i : Nat) (input : Array α) (output : Array α := #[]) : Array α :=
  if h : i < input.size then
    revFrom (i+1) input (output.push input[i])
  else output
termination_by
  revFrom i input _ => input.size - i

namespace Html

declare_syntax_cat html
declare_syntax_cat tag_name
declare_syntax_cat attrib
declare_syntax_cat attrib_val
scoped syntax str : attrib_val
scoped syntax "{{" term "}}" : attrib_val
scoped syntax ident "=" attrib_val : attrib
scoped syntax str "=" attrib_val : attrib
scoped syntax "class" "=" attrib_val : attrib

scoped syntax ident : tag_name
scoped syntax "section" : tag_name

partial def _root_.Lean.TSyntax.tagName : TSyntax `tag_name → String
  | ⟨.node _ _ #[.atom _ x]⟩ => x
  | ⟨.node _ _ #[.ident _ _ x ..]⟩ => x.eraseMacroScopes.toString
  | _ => "fake tag name!!!"


scoped syntax "{{" term "}}" : html
scoped syntax "<" tag_name attrib* ">" html* "</" tag_name ">" : html
scoped syntax  "<" tag_name attrib* "/" ">" : html
scoped syntax str : html
scoped syntax "s!" interpolatedStr(term) : html

scoped syntax "{{"  html+ "}}" : term
scoped syntax "{{{" attrib* "}}}" : term

open Lean.Macro in
macro_rules
  | `(term| {{{ $attrs* }}} ) => do
    let attrsOut ← attrs.mapM fun
      | `(attrib| $name:ident = $val:str) => `(term| ($(quote name.getId.toString), $val))
      | `(attrib| $name:ident = {{ $e }} ) => `(term| ($(quote name.getId.toString), $e))
      | `(attrib| $name:str = {{ $e }} ) => `(term| ($(quote name.getString), $e))
      | `(attrib| class = $val:str) => `(term| ("class", $val))
      | `(attrib| class = {{ $e }}) => `(term| ("class", $e))
      | _ => throwUnsupported
    `(term| #[ $[$attrsOut],* ] )
  | `(term| {{ {{ $e:term }} }} ) => ``(($e : Html))
  | `(term| {{ $s:str }} ) => ``(Html.text $s)
  | `(term| {{ s! $s:interpolatedStr }} ) => ``(Html.text s!$s)
  | `(term| {{ $html1:html $html2:html $htmls:html*}}) =>
    `({{$html1}} ++ {{$html2}} ++ Html.seq #[$[{{$htmls}}],*])
  | `(term| {{ <$tag:tag_name $[$extra]* > $content:html </ $tag':tag_name> }}) => do
    if tag.tagName != tag'.tagName then
      Macro.throwErrorAt tag' s!"Mismatched closing tag, expected {tag.tagName} but got {tag'.tagName}"
    ``(Html.tag $(quote tag.tagName) {{{ $extra* }}} {{ $content }} )
  | `(term| {{ <$tag:tag_name $[$extra]* > $[$content:html]* </ $tag':tag_name> }}) => do
    if tag.tagName != tag'.tagName then
      Macro.throwErrorAt tag' s!"Mismatched closing tag, expected {tag.tagName} but got {tag'.tagName}"
    ``(Html.tag $(quote tag.tagName) {{{ $extra* }}} <| Html.fromArray #[$[ {{ $content }} ],*] )
  | `(term| {{ <$tag:tag_name $[$extra]* /> }}) => ``(Html.tag $(quote tag.tagName) {{{ $extra* }}} Html.empty )

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
  (LeanDoc.Html.tag
    "body"
    #[("lang", "en"), ("class", "thing")]
    (LeanDoc.Html.tag "p" #[] (LeanDoc.Html.text "foo bar")))
-/
#guard_msgs in
  #eval test

open Std.Format in
partial def format : Html → Std.Format
  | .text str => .text (str.replace "<" "&lt;" |>.replace ">" "&gt;")
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

partial def asString : Html → String
  | .text str => str.replace "<" "&lt;" |>.replace ">" "&gt;"
  | .tag name attrs (.seq #[]) =>
    "<" ++ name ++ attrsAsString attrs ++ "/>"
  | .tag name attrs (.seq #[subElem]) =>
    "<" ++ name ++ attrsAsString attrs ++ ">" ++ asString subElem ++ s!"</{name}>"
  | .tag "pre" attrs body =>
    "<pre" ++ attrsAsString attrs ++ ">\n" ++
    Html.asString body ++ "\n" ++
    "</pre>"
  | .tag name attrs body =>
      "<" ++ name ++ attrsAsString attrs ++ ">" ++
      Html.asString body ++
      s!"</{name}>"
  | .seq elts => String.join (elts.toList.map Html.asString)
where
  attrsAsString xs := String.join <| xs.toList.map (fun ⟨k, v⟩ => s!" {k}=\"{v}\"")
