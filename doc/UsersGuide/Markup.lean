/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.DocString.Syntax
import VersoManual

set_option guard_msgs.diff true

open Verso Genre Manual

section
open Lean
open Lean.Doc.Syntax

variable [Monad m] [MonadError m] [MonadQuotation m]

def newlinesToSpace (inls : Array (TSyntax `inline)) : m (Array (TSyntax `inline)) := do
  let mut out := #[]
  for h : i in [:inls.size] do
    match inls[i] with
    | inl@`(inline|line!$s) =>
      if i < inls.size - 1 then
        out := out.push (←  `(inline| " "))
      else
        out := out.push inl
    | inl => out := out.push inl
  return out

def log10 (n : Nat) : Nat :=
  if n ≥ 10 then
    log10 (n / 10) + 1
  else 0

def asCode (s : String) : String :=
  let lines := s.dropEndWhile (· == '\n') |>.split (· == '\n') |>.toList
  let lw := log10 lines.length + 1
  let pad (s : String) : String :=
    (lw - s.length).fold (init := s) fun _ _ => (" " ++ ·)
  (lines.mapIdx fun i l => (s!"{toString (i + 1) |> pad}|{l}⏎\n")) |> String.join |>.trimAsciiEnd |>.copy

partial def preview (stx : Syntax) : m Std.Format :=
  match stx with
  | `(inline| $s:str) => pure <| Format.joinSep (s.getString.splitOn " ") .line
  | `(inline| line! $_s:str) => pure .line
  | `(inline| _[ $s:inline* ]) => do
    let s ← newlinesToSpace s
    let contents ← s.toList.mapM (preview ∘ TSyntax.raw)
    pure <| .group <| .nest 2 ("<emph>" ++ .line ++ .fill (.join contents)) ++ .line ++ "</emph>"
  | `(inline| *[ $s:inline* ]) => do
    let s ← newlinesToSpace s
    let contents ← s.toList.mapM (preview ∘ TSyntax.raw)
    pure <| .fill <| "<bold>" ++ .join contents ++ "</bold>"
  | `(inline| role{$x $args*}[$inls*]) => do
    let inls ← newlinesToSpace inls
    let args ← args.toList.mapM (preview ·.raw)
    let contents ← inls.toList.mapM (preview ∘ TSyntax.raw)
    pure <| .fill <| .group (.nest 2 (s!"<{x.getId.toString} {Format.joinSep args " " |>.pretty}>" ++ .line ++ .fill (Format.joinSep contents .line)) ++ .line ++ s!"</{x.getId.toString}>")
  | `(inline| \math code($s)) =>
    pure <| s!"<math contents={s.getString.quote}/>"
  | `(inline| \displaymath code($s)) =>
    pure <| s!"<displaymath contents={s.getString.quote}/>"
  | `(inline| link[ $txt:inline* ]( $url:str )) => do
    let txt ← newlinesToSpace txt
    let contents ← txt.toList.mapM (preview ∘ TSyntax.raw)
    pure <| .group <| .nest 2 (s!"<a href=\"{url.getString}\">" ++ .line ++ .fill (.join contents)) ++ .line ++ "</a>"
  | `(inline| link[ $txt:inline* ][ $tgt:str ]) => do
    let txt ← newlinesToSpace txt
    let contents ← txt.toList.mapM (preview ∘ TSyntax.raw)
    pure <| .fill <| s!"<a href=\"(value of «{tgt.getString}»)\">" ++ .join contents ++ "</a>"
  | `(inline| image($s)($tgt:str)) => do
    pure <| .group <| .nest 2 <| "<img" ++ .line ++ s!"src=\"{tgt.getString}\"" ++ .line ++ s!"alt=\"{s.getString}\"/>"
  | `(inline| image($s)[$tgt:str]) => do
    pure <| .group <| .nest 2 <| "<img" ++ .line ++ s!"src=\"value of «{tgt.getString}»\"" ++ .line ++ s!"alt=\"{s.getString}\"/>"
  | `(inline| code( $code:str )) =>
    pure s!"<code>{code.getString.quote}</code>"
  | `(block| para[ $i:inline* ]) => do
    let contents ← i.toList.mapM (preview ∘ TSyntax.raw)
    pure <| .group <| .nest 2 ("<p>" ++ .line ++ .fill (.join contents)) ++ .line ++ "</p>"
  | `(block| > $bs*) => do
    let contents ← bs.toList.mapM (preview ∘ TSyntax.raw)
    pure <| .group <| .nest 2 ("<blockquote>" ++ .line ++ .fill (Format.joinSep contents .line)) ++ .line ++ "</blockquote>"
  | `(block| [ $ref:str ]: $url:str) =>
    pure <| .group <| .nest 2 <| "where" ++ .line ++ .group (.nest 2 (s!"«{ref.getString}» :=" ++ .line ++ url.getString))
  | `(block| header($n){$inls*}) => do
    let title ← Format.join <$> inls.toList.mapM (preview ∘ TSyntax.raw)
    pure <| s!"<h{n.getNat + 1}>" ++ title.fill ++ s!"</h{n.getNat + 1}>" ++ Format.line
  | `(block| ``` | $s ```) =>
    pure <| .nest 2 (s!"<codeblock>" ++ .line ++ asCode s.getString ++ .text "") ++ .line ++ s!"</codeblock>"
  | `(block| ```$x $args* | $s ```) => do
    let args ← args.toList.mapM (preview ·.raw)
    pure <| .nest 2 (s!"<{x.getId.toString} {Std.Format.prefixJoin " " args |>.pretty}>" ++ .line ++ asCode s.getString ++ .nil) ++ .line ++ s!"</{x.getId}>"
  | `(block| ::: $x $args* {$body*}) => do
    let args ← args.toList.mapM (preview ·.raw)
    let body ← body.toList.mapM (preview ·.raw)
    pure <| .group <| .nest 2 (s!"<{x.getId.toString} {Std.Format.prefixJoin " " args |>.pretty}>" ++ .line ++ Format.joinSep body .line) ++ .line ++ s!"</{x.getId.toString}>"
  | `(block| command{$x $args*}) => do
    let args ← args.toList.mapM (preview ·.raw)
    pure s!"<{x.getId.toString} {Std.Format.prefixJoin " " args |>.pretty}/>"
  | `(doc_arg|($x:ident := $v)) | `(doc_arg|$x:ident := $v) => do
    pure <| s!"{x.getId.toString}=\"{← preview v.raw}\""
  | `(doc_arg|$v:arg_val) => preview v.raw
  | `(arg_val|$v:ident) => pure s!"{v.getId}"
  | `(arg_val|$v:num) => pure s!"{v.getNat}"
  | `(arg_val|$v:str) => pure s!"{v.getString.quote}"
  | `(block| ul{$lis*}) => do
    let items ← lis.toList.mapM (preview ·.raw)
    pure <| .group <| .nest 2 ("<ul>" ++ .line ++ Format.joinSep items .line) ++ .line ++ "</ul>"
  | `(block| ol($_n){$lis*}) => do
    let items ← lis.toList.mapM (preview ·.raw)
    pure <| .group <| .nest 2 ("<ol>" ++ .line ++ Format.joinSep items .line) ++ .line ++ "</ol>"
  | `(block| dl{$descs*}) => do
    let items ← descs.toList.mapM fun x => (preview x.raw) <&> ("  " ++ · ++ "\n")
    pure <| .group <| .nest 2 <| ("<dl>" ++ .line ++ Format.joinSep items .line) ++ .line ++ "</dl>"
  | `(desc| : $dt* => $dd* ) => do
    let dt ← dt.toList.mapM (preview ·.raw)
    let dd ← dd.toList.mapM (preview ·.raw)
    pure <|
      .group (.nest 2 ("<dt>" ++ .line ++ .join dt) ++ .line ++ "</dt>") ++ .line ++
      .group (.nest 2 ("<dd>" ++ .line ++ .join dd) ++ .line ++ "</dd>")
  | `(li| * $content*) => do
    let content ← content.toList.mapM (preview ∘ TSyntax.raw)
    pure <| .group <| .nest 2 ("<li>" ++ .line ++ .join content) ++ .line ++ "</li>"
  | other => do
    if other.getKind = nullKind then
      pure <| .joinSep (← other.getArgs.toList.mapM preview) (.line ++ .line)
    else
      throwErrorAt stx "Didn't understand {Verso.SyntaxUtils.ppSyntax stx} for preview"
end

block_extension MarkupExample (title : String) where
  data := title
  traverse _ _ _ := pure none
  toHtml := some fun _goI goB _id data contents => open Verso.Output.Html in do
    let .str title := data
      | Verso.Doc.Html.HtmlT.logError s!"Expected a string, got {data.compress}"
        return .empty
    let #[stx, parsed] := contents
      | Verso.Doc.Html.HtmlT.logError s!"Expected two blocks, got {contents.size}"
        return .empty
    pure {{
      <div class="markup-example">
        <div class="markup-example-header">{{ title }}</div>
        <div class="content">
          <div class="syntax">
            <div class="title">"Verso Markup"</div>
            {{← goB stx}}
          </div>
          <div class="result">
            <div class="title">"Result"</div>
            {{← goB parsed}}
          </div>
        </div>
      </div>
    }}
  localContentItem _id data _contents := open Verso.Output.Html in do
    let .str title := data
      | throw s!"Expected a title string, got {data.compress}"
    pure #[(title, {{ {{title}} }})]
  extraCss := [
r#"
.markup-example {
  border: 1px solid #98B2C0;
  border-radius: 0.5rem;
  margin-bottom: var(--verso--box-vertical-margin);
  margin-top: var(--verso--box-vertical-margin);
  overflow: hidden;
}

.markup-example-header {
  font-style: italic;
  font-family: var(--verso-structure-font-family);
  padding: var(--verso--box-padding);
}

.markup-example-header * {
  margin: 0;
}

.markup-example > .content {
  display: flex;
}

.markup-example > .content > .syntax, .markup-example > .content > .result {
  flex: 1;
  padding: 0 var(--verso--box-padding);
  position: relative;
  width: calc(50% - calc(4 * var(--verso--box-padding)));
}

.markup-example > .content > .syntax pre, .markup-example > .content > .result pre {

}

.markup-example > .content > .syntax > .title, .markup-example > .content > .result > .title {
  font-family: var(--verso-structure-font-family);
  padding: 0;
  font-size: 0.875rem;
}

@media screen and (max-width: 700px) {
  .markup-example > .content {
    flex-direction: column;
  }

  .markup-example > .content > .syntax, .markup-example > .content > .result {
    width: calc(100% - calc(2 * var(--verso--box-padding)));
  }
}
"#
  ]
  toTeX := some fun _goI _goB _id data contents => open Verso.Output.TeX in open Verso.Doc.TeX in do
    let .str title := data
      | logError s!"Expected title as string, got {data.compress}"
        return \TeX{}
    let #[.code stx, .code parsed] := contents
      | logError s!"Expected two code blocks, got {contents.size}"
        return \TeX{}
    pure \TeX{
      \begin{markupexample}{\Lean{title}}
        \begin{syntaxpanel}\Lean{.raw stx}\end{syntaxpanel}
        \columnbreak
        \begin{resultpanel}\Lean{.raw parsed}\end{resultpanel}
      \end{markupexample}
    }
  usePackages := ["\\usepackage{multicol}", "\\usepackage{float}"]
  preamble := [
r#"
\newfloat{syntaxexample}{htbp}{loe}
\floatname{syntaxexample}{Markup Example}

\DefineVerbatimEnvironment{syntaxpanel}{Verbatim}{
    frame=topline,
    framesep=8pt,
    fontsize=\footnotesize,
    label={\normalfont\bfseries\small Syntax},
    labelposition=topline
}

\DefineVerbatimEnvironment{resultpanel}{Verbatim}{
    frame=topline,
    framesep=8pt,
    fontsize=\footnotesize,
    label={\normalfont\bfseries\small Result},
    labelposition=topline
}

\newenvironment{markupexample}[1]{%
    \begin{syntaxexample}
    \centering
    \caption{#1}
    \setlength{\columnsep}{1em}
    \begin{multicols}{2}
}{%
    \end{multicols}
    \end{syntaxexample}
}

"#
  ]


section
open Lean
open ArgParse
open Doc.Elab

structure MarkupPreviewConfig where
  title : StrLit

instance : FromArgs MarkupPreviewConfig DocElabM where
  fromArgs := MarkupPreviewConfig.mk <$> .positional `title .strLit

end

private def withNl (s : String) : String := if s.endsWith "\n" then s else s.push '\n'


open Verso Doc Elab in
open Lean Elab in
open Verso.Parser in
open Lean.Doc.Syntax in
@[directive]
def markupPreview : DirectiveElabOf MarkupPreviewConfig
  | {title}, contents => do
    let #[blk1, blk2] := contents.filter nonempty
      | throwError "Expected precisely two code blocks, got {contents.filter nonempty}"
    let `(block|``` | $contents ```) := blk1
      | throwErrorAt blk1 "Expected anonymous code block"
    let `(block|``` | $expected ```) := blk2
      | throwErrorAt blk1 "Expected anonymous code block"

    let stx ← blocks {} |>.parseString contents.getString.trimAsciiEnd.copy
    let p ← preview stx
    let p := p.pretty (width := 35)

    withOptions (verso.code.warnLineLength.set · 35) do
      warnLongLines none contents
      warnLongLines none expected

    unless eq expected.getString p do
      let hint ← MessageData.hint m!"Replace with actual output" #[withNl p] (ref? := expected)
      throwErrorAt expected m!"Expected {indentD expected.getString} but got {indentD p}\n{hint}"

    Hover.addCustomHover contents s!"```\n{p}\n```"
    return .other (← ``(MarkupExample $(quote title.getString))) #[
      .code contents.getString,
      .code p
    ]
where
  eq (s1 s2 : String) : Bool :=
    let lines1 := s1.trimAscii.split (· == '\n') |>.map (·.trimAsciiEnd) |>.toArray
    let lines2 := s2.trimAscii.split (· == '\n') |>.map (·.trimAsciiEnd) |>.toArray
    lines1 == lines2

  nonemptyI : TSyntax `inline → Bool
  | `(inline|$s:str) | `(inline|line!$s) => !s.getString.isEmpty
  | _ => true
  nonempty : TSyntax `block → Bool
  | `(block|para[$inls*]) => inls.any nonemptyI
  | _ => true

open Lean Verso Doc Elab in
open Verso.Parser in
@[code_block markupPreview]
def markupPreviewPre : CodeBlockExpanderOf MarkupPreviewConfig
  | {title}, contents => do

    let stx ← blocks {} |>.parseString contents.getString
    let p ← preview stx
    let p := p.pretty (width := 35)

    let directive := s!":::markupPreview {title.getString.quote}\n```\n{withNl contents.getString}```\n```\n{withNl p}```\n:::"
    let hint ← MessageData.hint m!"Replace with directive:" #[directive]
    throwError m!"Expected a directive.{hint}"



#doc (Manual) "Verso Markup" =>
%%%
tag := "verso-markup"
htmlSplit := .never
%%%

Lean's documentation markup language is a close relative of Markdown, but it's not identical to it.

# Design Principles
%%%
tag := "markup-design-principles"
%%%

: Syntax errors

  Fail fast rather than producing unexpected output or having complicated rules.

: Reduce lookahead

  Parsing should succeed or fail as locally as possible.

: Extensibility

  There should be dedicated features for compositionally adding new kinds of content, rather than relying on a collection of ad-hoc textual subformats.

: Assume Unicode

  Lean users are used to entering Unicode directly and have good tools for it, so there's no need to support alternative textual syntaxes for characters not on keyboards such as em dashes or typographical quotes.

: Markdown compatibility

  Users benefit from existing muscle memory and familiarity when it doesn't lead to violations of the other principles.

# Syntax
%%%
tag := "markup-syntax"
%%%

Like Markdown, Lean's markup has three primary syntactic categories:


: Document structure

 Headers, footnote definitions, and named links give greater structure to a document. They may not be nested inside of blocks.


: Block elements

 The main organization of written text, including paragraphs, lists, and quotations. Some blocks may be nested: for example, lists may contain other lists.

: Inline elements

 The ordinary content of written text, such as text itself, bold or emphasized text, and hyperlinks.


## Document Structure
%%%
tag := "document-structure"
%%%

Documents are organized into {deftech}_parts_.
A part is a logical division of the content of the document, such as a chapter, section, subsection, or volume.
Parts may have associated metadata, such as authors, publication dates, internal identifiers for cross-referencing, or desired URLs; the specific metadata associated with a part is determined by the document's {tech}[genre].

A part contains a sequence of blocks followed by a sequence of sub-parts, either of which may be empty.

A part is introduced with a {deftech}_header_.
Headers consist of one or more hash marks (`#`) at the beginning of a line followed by a sequence of inlines.
The number of hash marks indicates the nesting of a header, and headers with more hash marks indicate parts at a lower level.
A lower-level header introduces a sub-part of the preceding header, while a header at a level at least as high as the preceding header terminates that part.
In other words, header levels induce a tree structure on the document.

Headers must be well-nested: the first header in a document must have exactly one hash mark, and all subsequent headers may have at most one more hash mark than the preceding header.
This is a _syntactic_ requirement: regardless of whether a Verso file contains the text of a whole book, a chapter, or just a single section, its outermost header must be introduced with a single hash mark.
Headers indicate the logical nesting structure of the document, rather than the headers to be chosen when rendering the document to output formats such as HTML.

Metadata may be associated with a header by following it with a {deftech}_metadata block_.
Metadata blocks begin and end with `%%%`, and they contain any syntax that would be acceptable in a Lean structure initializer.

:::markupPreview "Header"
```
# Top-Level Header
```
```
<h1>Top-Level Header</h1>
```
:::

:::markupPreview "Blah"
```
a b c
```
```
<p> a b c </p>
```
:::


## Block Syntax
%%%
tag := "block-syntax"
%%%

Paragraphs are undecorated: any sequence of inlines that is not another block is a paragraph.
Paragraphs continue until a {deftech}_blank line_ (that is, a line containing only whitespace) or another block begins:

:::markupPreview "Paragraphs"
```
This is one paragraph.
Even though this sentence is on a
new line, the paragraph continues.

This is a new paragraph.
* This list stopped the paragraph.
* As in Markdown and SGML, lists
  are not part of paragraphs.
```
```
<p>
  This is one paragraph. Even
  though this sentence is on a new
  line, the paragraph continues.
</p>

<p> This is a new paragraph. </p>

<ul>
  <li>
    <p>
      This list stopped the
      paragraph.
    </p>
  </li>
  <li>
    <p>
      As in Markdown and SGML,
      lists   are not part of
      paragraphs.
    </p>
  </li>
</ul>
```
:::

### Lists
%%%
tag := "list-syntax"
%%%

There are three kinds of lists:

: Unordered lists

  Unordered lists indicate that the order of the items in the list is not of primary importance.
  They correspond to `<ul>` in HTML or `\begin{itemize}` in LaTeX.

: Ordered lists

  Unordered lists indicate that the order of the items in the list is important.
  They correspond to `<ol>` in HTML or `\begin{enumerate}` in LaTeX.

: Description lists

  Description lists associate a term with more information. This very list is a description list.
  They correspond to `<dl>` in HTML or `\begin{description}` in LaTeX.

A line that begins with zero or more spaces followed by a `*`, `-`, or `+` starts an item of an unordered list.
This character is called the {deftech}_list item indicator_.
Subsequent items are part of the same list if they use the same indicator character and have the same indentation.
Any subsequent blocks whose first character is indented further than the indicator are part of the item itself; items may contain multiple blocks, or even other lists.

:::markupPreview "Unordered Lists"
```
* A list with two items
* They both start in column 0
```
```
<ul>
  <li>
    <p> A list with two items </p>
  </li>
  <li>
    <p>
      They both start in column 0
    </p>
  </li>
</ul>
```
:::

:::markupPreview "Indented Unordered Lists"
```
 * A list with two items
 * They both start in column 1
```
```
<ul>
  <li>
    <p> A list with two items </p>
  </li>
  <li>
    <p>
      They both start in column 1
    </p>
  </li>
</ul>
```
:::

:::markupPreview "List Indicators"
```
 * Two lists
 + They have different indicators.
```
```
<ul>
  <li> <p> Two lists </p> </li>
</ul>

<ul>
  <li>
    <p>
      They have different
      indicators.
    </p>
  </li>
</ul>
```
:::


:::markupPreview "List Indentation Sensitivity"
```
 * A list with one element
* Another list, due to different
  indentation
```
```
<ul>
  <li>
    <p>
      A list with one element
    </p>
  </li>
</ul>

<ul>
  <li>
    <p>
      Another list, due to
      different   indentation
    </p>
  </li>
</ul>
```
:::

:::markupPreview "Sub-Lists"
```
* A list with one item.
  It contains this paragraph

  * And this other sub-list

  And this paragraph
```
```
<ul>
  <li>
    <p>
      A list with one item.   It
      contains this paragraph
    </p><ul>
      <li>
        <p>
          And this other sub-list
        </p>
      </li>
    </ul><p>
      And this paragraph
    </p>
  </li>
</ul>
```
:::

A line that starts with zero or more spaces, followed by one or more digits and then either a period (e.g. `1.`) or a closing parenthesis (`1)`), begins an item of an ordered list.
Like unordered lists, ordered lists are sensitive to both indentation and indicator characters.

:::markupPreview "Ordered Lists"
```
1. First, write a number.
2. Then, an indicator (`.` or `)`)
```
```
<ol>
  <li>
    <p> First, write a number. </p>
  </li>
  <li>
    <p>
      Then, an indicator
      (<code>"."</code> or
      <code>")"</code>)
    </p>
  </li>
</ol>
```
:::

:::markupPreview "Ordered Lists and Indicators"
```
1. Two lists
2) They have different indicators.
```
```
<ol>
  <li> <p> Two lists </p> </li>
</ol>

<ol>
  <li>
    <p>
      They have different
      indicators.
    </p>
  </li>
</ol>
```
:::

Description lists consist of a sequence of description items that have the same indentation.
A description item is a line that starts with zero or more spaces, followed by a colon, followed by a sequence of inlines and a blank line. After the blank line, there must be one or more blocks with indentation greater than the colon.

:::markupPreview "Description Lists"
```
: Item 1

  Description of item 1

: Item 2

  Description of item 2
```
```
<dl>
    <dt>  Item 1 </dt>
  <dd>
    <p> Description of item 1 </p>
  </dd>

    <dt>  Item 2 </dt>
  <dd>
    <p> Description of item 2 </p>
  </dd>
   </dl>
```
:::

### Quotes
%%%
tag := "quote-syntax"
%%%

Quotation blocks show that a sequence of blocks were spoken by someone other than the author. They consist of a line that starts with zero or more spaces, followed by a greater-than sign (`>`), followed by a sequence of blocks that are indented more than the greater-than sign.

:::markupPreview "Quotations"
```
It is said that:
> Quotations are excellent.

  This paragraph is part of the
  quotation.

 So is this one.

But not this one.
```
```
<p> It is said that: </p>

<blockquote>
  <p>
    Quotations are excellent.
  </p>
  <p>
    This paragraph is part of the
    quotation.
  </p>
  <p> So is this one. </p>
</blockquote>

<p> But not this one. </p>
```
:::

### Code Blocks
%%%
tag := "code-block-syntax"
%%%

{deftech}[Code blocks] begin with three or more back-ticks at the start of a line (they may be preceded by spaces).
This is referred to as a {deftech}_fence_.
They may optionally have a name and a sequence of arguments after the back-ticks.
The code block continues until a line that contains only the same number of back-ticks at the same indentation.
Every line in the code block must be at least as indented as the fence, and it denotes the string that results from removing the indentation from each line.
Code blocks may not contain a sequence of back-ticks that is at least as long as the fence; to add more back-ticks to the code block, the fence must be made larger.

:::markupPreview "Code Blocks"
````
```
This is a code block
with two lines
```
````
```
<codeblock>
  1|This is a code block⏎
  2|with two lines⏎
</codeblock>
```
:::

:::markupPreview "Code Blocks as Extensions"
````
```lean
-- This code block is named
-- `lean`. It was called with
-- no arguments.
def x := 5
```
````
```
<lean >
  1|-- This code block is named⏎
  2|-- `lean`. It was called with⏎
  3|-- no arguments.⏎
  4|def x := 5⏎
</lean>
```
:::

:::markupPreview "Indented Code Blocks"
````
  ```lean
  -- This indented code block
  -- denotes the de-indented
  -- string
  def x := 5
  ```
````
```
<lean >
  1|-- This indented code block⏎
  2|-- denotes the de-indented⏎
  3|-- string⏎
  4|def x := 5⏎
</lean>
```
:::


:::markupPreview "Code Blocks and Arguments"
````
```lean (error := true)
-- This code block is named
-- `lean`, called with the
-- named argument `error`
-- set to `true`.
def x : String := 5
```
````
```
<lean  error="true">
  1|-- This code block is named⏎
  2|-- `lean`, called with the⏎
  3|-- named argument `error`⏎
  4|-- set to `true`.⏎
  5|def x : String := 5⏎
</lean>
```
:::

When a code block has a name, then the name is resolved in the current Lean namespace and used to select an implementation.
The {ref "extensions"}[chapter on Verso markup extensions] has more details on this process.

### Directives
%%%
tag := "directive-syntax"
%%%

A {deftech}_directive_ is a kind of block with no meaning other than that assigned by extensions, akin to a custom environment in LaTeX or a `<div>` tag in HTML.
Directives begin with three or more colons and a name with zero or more arguments, and end with the same number of colons at the same indentation on a line by themselves.
They may contain any number of blocks, which must be indented at least as much as the colons.
Nested directives must begin and end with strictly fewer colons than the surrounding directives.

The {ref "extensions"}[chapter on Verso markup extensions] describes the processing of directives in more detail.

This is an empty directive:
:::markupPreview "Directives"
```
:::nothing
:::
```
```
<nothing >  </nothing>
```
:::

This directive contains a directive and a paragraph:
:::markupPreview "Nested Directives"
```
::::outer
:::inner
Hello
:::
This is a paragraph
::::
```
```
<outer >
  <inner > <p> Hello </p> </inner>
  <p> This is a paragraph </p>
</outer>
```
:::

### Commands
%%%
tag := "command-block-syntax"
%%%

A line that consists of only a set of curly braces that contain a name and zero or more arguments is a {deftech}_command_.
The name is used to select an implementation for the command, which is then invoked during elaboration.
The {ref "extensions"}[chapter on Verso markup extensions] has more details on this process.

:::markupPreview "Commands"
```
{include 0 MyChapter}
```
```
<include  0 MyChapter/>
```
:::


## Inline Syntax
%%%
tag := "inline-syntax"
%%%

Emphasis is written with underscores:
:::markupPreview "Emphasis"
```
Here's some _emphasized_ text
```
```
<p>
  Here's some
  <emph> emphasized </emph> text
</p>
```
:::
Emphasis can be nested by using more underscores for the outer emphasis:
:::markupPreview "Nested Emphasis"
```
Here's some __emphasized text
with _extra_ emphasis__ inside
```
```
<p>
  Here's some
  <emph>
    emphasized text with
    <emph> extra </emph> emphasis
  </emph>
  inside
</p>
```
:::

Strong emphasis (bold) is written with asterisks:
:::markupPreview "Strong Emphasis (Bold)"
```
Here's some *bold* text
```
```
<p>
  Here's some <bold>bold</bold>
  text
</p>
```
:::

Hyperlinks consist of the link text in square brackets followed by the target in parentheses:
:::markupPreview "Links"
```
[Lean](https://lean-lang.org)
```
```
<p>
  <a href="https://lean-lang.org">
    Lean
  </a>
</p>
```
:::

Link targets may also be named:

:::markupPreview "Named Link Targets"
```
The [Lean website][lean]

[lean]: https://lean-lang.org
```
```
<p>
  The
  <a href="(value of «lean»)">Lean
  website</a>
</p>

where
  «lean» := https://lean-lang.org
```
:::

Literal code elements are written in back-ticks.
The same number of back-ticks that opens a code element must be used to close it, and the code element may not contain a sequence of back-ticks that's at least as long as its opener and closer.

:::markupPreview "Literal Code"
```
The definition of `main`
```
```
<p>
  The definition of
  <code>"main"</code>
</p>
```
:::

As a special case, code inlines that being and end with a space denote the string that results from removing one leading and trailing space.
This makes it possible to represent values that begin or end with back-ticks:
:::markupPreview "Spaces in Code"
```
`` `quotedName ``
```
```
<p> <code>"`quotedName"</code> </p>
```
:::
or with spaces:
:::markupPreview "Multiple Spaces in Code"
```
``  one space  ``
```
```
<p> <code>" one space "</code> </p>
```
:::

::::paragraph
Images require both alternative text and an address for the image:
:::markupPreview "Images"
```
![Alt text](image.png)
```
```
<p>
  <img
    src="image.png"
    alt="Alt text"/>
</p>
```
:::
:::markupPreview "Named Image Addresses"
```
![Alternative text][image]

[image]: image.png
```
```
<p>
  <img
    src="value of «image»"
    alt="Alternative text"/>
</p>

where «image» := image.png
```
:::
::::


TeX math can be included using a single or double dollar sign followed by code. Two dollar signs results in display-mode math, so `` $`\sum_{i=0}^{10} i` `` results in $`\sum_{i=0}^{10} i` while `` $$`\sum_{i=0}^{10} i` `` results in: $$`\sum_{i=0}^{10} i`

A {deftech}_role_ indicates that subsequent inlines have a special meaning.
Roles can be used to trigger special handling of code (e.g. elaboration), register definitions and uses of technical terms, add marginal notes, and much more.
They correspond to custom commands in LaTeX.
A role consists of curly braces that contain a name and arguments, all on the same line, followed immediately either by a self-delimiting inline or by square brackets that contain zero or more inlines.

An inline is {deftech}_self-delimiting_ if it has distinct start and end tokens that make its ending position clear.
Emphasis, strong emphasis, code, links, images, math, and roles are self-delimiting.

::::paragraph
This role contains multiple inlines using square brackets:
:::markupPreview "Roles With Explicit Scope"
```
{ref "chapter-tag"}[the chapter on
$`\frac{1}{2}`-powered syntax]
```
```
<p>
  <ref "chapter-tag">
    the chapter on
    <math contents="\\frac{1}{2}"/>
    -powered syntax
  </ref>
</p>
```
:::

This one takes a single inline code element without needing square brackets:
:::markupPreview "Single-Argument Roles"
```
{lean}`2 + f 4`
```
```
<p>
  <lean >
    <code>"2 + f 4"</code>
  </lean>
</p>
```
:::
::::

# Differences from Markdown
%%%
tag := "differences-from-markdown"
%%%

This is a quick "cheat sheet" for those who are used to Markdown, documenting the differences.

## Syntax Errors
%%%
tag := "syntax-errors"
%%%

While Markdown includes a set of precedence rules to govern the meaning of mismatched delimiters (such as in `what _is *bold_ or emph*?`), these are syntax errors in Lean's markup.
Similarly, Markdown specifies that unmatched delimiters (such as `*` or `_`) should be included as characters, while Lean's markup requires explicit escaping of delimiters.

This is based on the principle that, for long-form technical writing, it's better to catch typos while writing than while reviewing the text later.

## Reduced Lookahead
%%%
tag := "reduced-lookahead"
%%%

In Markdown, whether `[this][here]` is a link depends on whether `here` is defined as a link reference target somewhere in the document.
In Lean's markup, it is always a link, and it is an error if `here` is not defined as a link target.

## Header Nesting
%%%
tag := "header-nesting"
%%%

In Lean's markup, every document already has a title, so there's no need to use the highest level header (`#`) to specify one.
Additionally, all documents are required to use `#` for their top-level header, `##` for the next level, and so forth, because a single file may represent a section, a chapter, or even a whole book.
Authors should not need to maintain a global mapping from header levels to document structures, so Lean's markup automatically assigns these based on the structure of the document.

## Genre-Specific Extensions
%%%
tag := "genre-specific-extensions"
%%%

Markdown has no standard way for specific tools or styles of writing to express domain- or {ref "genres"}[genre]-specific concepts.
Lean's markup provides standard syntaxes to use for this purpose, enabling compositional extensions.

## Fewer Unused Features
%%%
tag := "removed-md-features"
%%%

Markdown has a number of features that are rarely used in practice.
They have been removed from Verso to reduce surprises while using it and make documents more predictable.
This includes:
 * the distinction between [tight](https://spec.commonmark.org/0.31.2/#tight) and [loose](https://spec.commonmark.org/0.31.2/#loose) lists,
 * [four-space indentation](https://spec.commonmark.org/0.31.2/#indented-code-blocks) to create code blocks,
 * [Setext-style headers](https://spec.commonmark.org/0.31.2/#setext-headings), indicated with underlines instead of leading hash marks (`#`),
 * [hard line break syntax](https://spec.commonmark.org/0.31.2/#hard-line-breaks),
 * and [HTML entities and character references](https://spec.commonmark.org/0.31.2/#entity-and-numeric-character-references)

Other Markdown features don't make sense for non-HTML output, and can be implemented by a {tech}[genre] using code blocks or directives.
They have also been removed from Verso.
In particular, this includes [HTML blocks](https://spec.commonmark.org/0.31.2/#html-blocks), [raw HTML](https://spec.commonmark.org/0.31.2/#raw-html) and [thematic breaks](https://spec.commonmark.org/0.31.2/#thematic-breaks).

Finally, some Markdown features are used by a minority of authors, and make sense in all backends, but were not deemed worth the complexity budget.
In particular, this includes [auto-links](https://spec.commonmark.org/0.31.2/#autolinks).
