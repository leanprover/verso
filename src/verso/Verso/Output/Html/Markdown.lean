/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Html
public import MD4Lean
-- This line ensures that downstream clients get the cached olean correctly.
public import Verso.Output.Html.Entities
public import Verso.Markdown

set_option linter.missingDocs true
set_option doc.verso true

open Lean (Html)
open Verso.Markdown (HeaderMapping)

namespace Verso.Output.Html.Markdown

/-- The URL schemes that links may use. -/
def linkSchemes : List String := ["http", "https", "mailto"]

/-- The URL schemes that images may use. Images may also be embedded as {lit}`data` URLs. -/
def imageSchemes : List String := linkSchemes ++ ["data"]

/-- Returns the URL if it is relative or uses one of the given schemes. -/
def allowedUrl? (schemes : List String) (url : String) : Option String :=
  let compact := String.ofList (url.toList.filter (·.toNat > 0x20))
  let beforeDelim := compact.toList.takeWhile (fun c => c != ':' && c != '/' && c != '?' && c != '#')
  if beforeDelim.length < compact.length && compact.toList[beforeDelim.length]? == some ':' then
    if schemes.contains (String.ofList beforeDelim).toLower then some url else none
  else some url

/-- Converts attribute text, such as a link destination, to a string with its entities decoded. -/
public def attrText (xs : Array MD4Lean.AttrText) : String :=
  xs.foldl (init := "") fun s x =>
    match x with
    | .normal t => s ++ t
    | .entity e => s ++ (decodeEntity? e |>.getD e)
    | .nullchar => s.push '�'

/-- Returns a {lit}`title` attribute for non-empty title text. -/
def titleAttr (title : Array MD4Lean.AttrText) : Array (String × String) :=
  let t := attrText title
  if t.isEmpty then #[] else #[("title", t)]

mutual
  /-- Renders an inline Markdown element. -/
  public partial def text : MD4Lean.Text → Html
    | .normal s => .text s
    | .nullchar => .text "�"
    | .br _ => html%{<br/>}
    | .softbr s => .text s
    | .entity e => .text (decodeEntity? e |>.getD e)
    | .em xs => html%{<em>{texts xs}</em>}
    | .strong xs => html%{<strong>{texts xs}</strong>}
    | .del xs => html%{<del>{texts xs}</del>}
    | .u xs => texts xs
    | .wikiLink _ xs => texts xs
    | .a href title _ xs =>
      match allowedUrl? linkSchemes (attrText href) with
      | some url => html%{<a href={url} {...titleAttr title}>{texts xs}</a>}
      | none => texts xs
    | .img src title alt =>
      match allowedUrl? imageSchemes (attrText src) with
      | some url => html%{<img src={url} alt={plain alt} {...titleAttr title}/>}
      | none => texts alt
    | .code c => html%{<code>{String.join c.toList}</code>}
    | .latexMath xs => html%{<code class="math inline">{String.join xs.toList}</code>}
    | .latexMathDisplay xs => html%{<code class="math display">{String.join xs.toList}</code>}

  /-- Renders a sequence of inline Markdown elements. -/
  public partial def texts (xs : Array MD4Lean.Text) : Html :=
    .seq (xs.map text)

  /-- Extracts the plain text from inline Markdown elements, such as for an image's alt text. -/
  public partial def plain (xs : Array MD4Lean.Text) : String :=
    xs.foldl (init := "") fun s => fun
      | .normal t | .softbr t => s ++ t
      | .entity e => s ++ (decodeEntity? e |>.getD e)
      | .code c | .latexMath c | .latexMathDisplay c => s ++ String.join c.toList
      | .em ys | .strong ys | .del ys | .u ys | .wikiLink _ ys | .a _ _ _ ys | .img _ _ ys =>
        s ++ plain ys
      | .br _ | .nullchar => s

end

/--
Renders a header at nesting depth {name}`depth`, as computed by {name}`HeaderMapping.addHeader`.

Depth 0 is a heading element at level {name}`topLevel`, such as {lit}`h2` when {name}`topLevel` is
2, and each further depth is one level lower. A {name}`topLevel` of 0 is the same as 1. Headers that
are too deep for {lit}`h6` are paragraphs with strong emphasis.
-/
public def header (depth : Nat) (attrs : Array (String × String)) (contents : Html)
    (topLevel : Nat := 1) : Html :=
  let level := max topLevel 1 + depth
  if level ≤ 6 then .element s!"h{level}" attrs contents
  else html%{<p {...attrs}><strong>{contents}</strong></p>}

mutual
  /--
  Renders a block-level Markdown element. The state contains the headers that enclose the block.

  Headers are rendered with {name}`header`, starting at heading level {name}`topLevel`.
  -/
  public partial def block (b : MD4Lean.Block) (topLevel : Nat := 1) : StateM HeaderMapping Html :=
    match b with
    | .p xs => pure html%{<p>{texts xs}</p>}
    | .ul tight _ items => do
      let items ← items.mapM (listItem · tight topLevel)
      pure html%{<ul>{items}</ul>}
    | .ol tight start _ items => do
      let startAttr := if start == 1 then #[] else #[("start", toString start)]
      let items ← items.mapM (listItem · tight topLevel)
      pure html%{<ol {...startAttr}>{items}</ol>}
    | .hr => pure html%{<hr/>}
    | .header level xs => do
      let depth ← modifyGet (·.addHeader level)
      pure (header depth #[] (texts xs) topLevel)
    | .code _ _ _ ss => pure html%{<pre><code>{String.join ss.toList}</code></pre>}
    -- `Markdown.toHtml` parses with `MD_FLAG_NOHTML`, so its documents don't actually contain HTML
    -- blocks.  This case won't occur in practice:
    | .html ss => pure html%{<pre>{String.join ss.toList}</pre>}
    | .blockquote bs => do pure html%{<blockquote>{← blocks bs topLevel}</blockquote>}
    | .table hd rows =>
      pure html%{
        <table>
          <thead><tr>{hd.map fun h => html%{<th>{texts h}</th>}}</tr></thead>
          <tbody>
            {rows.map fun r => html%{<tr>{r.map fun c => html%{<td>{texts c}</td>}}</tr>}}
          </tbody>
        </table>
      }

  /-- Renders a sequence of block-level Markdown elements. -/
  public partial def blocks (bs : Array MD4Lean.Block) (topLevel : Nat := 1) :
      StateM HeaderMapping Html :=
    .seq <$> bs.mapM (block · topLevel)

  /--
  Renders a list item. In a tight list, the item's paragraphs are rendered without {lit}`p`
  elements.
  -/
  partial def listItem (item : MD4Lean.Li MD4Lean.Block) (tight : Bool) (topLevel : Nat) :
      StateM HeaderMapping Html := do
    let contents ← item.contents.mapM fun
      | .p xs => if tight then pure (texts xs) else block (.p xs) topLevel
      | b => block b topLevel
    pure html%{<li>{contents}</li>}
end

open MD4Lean in
/--
Returns the Markdown parser flags for CommonMark extended with tables and links for bare URLs. When
{name}`math` is true, LaTeX math in dollar signs is parsed as math.

HTML is parsed as text.
-/
def flags (math : Bool) : UInt32 :=
  let base :=
    MD_DIALECT_COMMONMARK ||| MD_FLAG_TABLES ||| MD_FLAG_PERMISSIVEURLAUTOLINKS ||| MD_FLAG_NOHTML
  if math then base ||| MD_FLAG_LATEXMATHSPANS else base

/--
Parses Markdown in CommonMark, extended with tables and links for bare URLs. When {name}`math` is
true, LaTeX math in dollar signs is parsed as math.

HTML in the Markdown is parsed as text.
-/
public def parse (markdown : String) (math : Bool := false) : Option MD4Lean.Document :=
  MD4Lean.parse markdown (flags math)

/--
Renders a Markdown string to HTML after parsing it with {name}`parse`.

Headers start at heading level {name}`topLevel`, as described for {name}`header`. Math is written
in the same {lit}`code` elements that Verso uses for math elsewhere. If the Markdown parser fails,
then the string is shown as preformatted text.
-/
public def toHtml (markdown : String) (math : Bool := false) (topLevel : Nat := 1) : Html :=
  match parse markdown (math := math) with
  | some doc => (blocks doc.blocks topLevel).run' []
  | none => html%{<pre>{markdown}</pre>}
