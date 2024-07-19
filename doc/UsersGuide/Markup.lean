import Verso.Syntax
import Verso.Genre.Manual

set_option guard_msgs.diff true

open Verso Genre Manual

open Lean in
open Verso.Syntax in
partial def preview [Monad m] [MonadError m] (stx : Syntax) : m String :=
  match stx with
  | `(inline| $s:str) => pure s.getString
  | `(inline| line! $s:str) => pure s.getString
  | `(inline| _{ $s:inline* }) => do
    let contents ← s.toList.mapM (preview ∘ TSyntax.raw)
    pure <| "<emph>" ++ String.join contents ++ "</emph>"
  | `(inline| *{ $s:inline* }) => do
    let contents ← s.toList.mapM (preview ∘ TSyntax.raw)
    pure <| "<bold>" ++ String.join contents ++ "</bold>"
  | `(inline| link[ $txt:inline* ]( $url:str )) => do
    let contents ← txt.toList.mapM (preview ∘ TSyntax.raw)
    pure s!"<a href=\"{url.getString}\">{String.join contents}</a>"
  | `(inline| link[ $txt:inline* ][ $tgt:str ]) => do
    let contents ← txt.toList.mapM (preview ∘ TSyntax.raw)
    pure s!"<a href=\"(value of «{tgt.getString}»)\">{String.join contents}</a>"
  | `(inline| code{ $code:str }) =>
    pure s!"<code>{code.getString}</code>"
  | `(block| para{ $i:inline* }) => do
    let contents ← i.toList.mapM (preview ∘ TSyntax.raw)
    pure <| String.join contents
  | `(block| [ $ref:str ]: $url:str) =>
    pure s!"where «{ref.getString}» := {url.getString}"
  | other => do
    if other.getKind = nullKind then
      pure <| String.join <| (← other.args.toList.mapM preview).intersperse "\n\n"
    else
      throwErrorAt stx "Didn't understand {Verso.SyntaxUtils.ppSyntax stx} for preview"

open Lean Verso Doc Elab Parser in
@[code_block_expander markupPreview]
def markupPreview : CodeBlockExpander
  | #[], contents => do
    let stx ← blocks {} |>.parseString contents.getString
    let p ← preview stx
    pure #[
      ← ``(Block.code $(quote contents.getString)),
      ← ``(Block.code $(quote <| toString <| p))
    ]
  | _, contents => throwErrorAt contents "Unexpected arguments"


#doc (Manual) "Lean Markup" =>

Lean's documentation markup language is a close relative of Markdown, but it's not identical to it.

# Design Principles

 1. Syntax errors - fail fast rather than producing unexpected output or having complicated rules
 2. Reduce lookahead - parsing should succeed or fail as locally as possible
 3. Extensibility - there should be dedicated features for compositionally adding new kinds of content, rather than relying on a collection of ad-hoc textual subformats
 4. Assume Unicode - Lean users are used to entering Unicode directly and have good tools for it, so there's no need to support alternative textual syntaxes for characters not on keyboards such as em dashes or typographical quotes
 5. Markdown compatibility - benefit from existing muscle memory and familiarity when it doesn't lead to violations of the other principles
 6. Pandoc and Djot compatibility - when Markdown doesn't have a syntax for a feature, attempt to be compatible with Pandoc Markdown or Djot

# Syntax

Like Markdown, Lean's markup has three primary syntactic categories:

: Inline elements

 The ordinary content of written text, such as text itself, bold or emphasized text, and hyperlinks.

: Block elements

 The main organization of written text, including paragraphs, lists, and quotations. Some blocks may be nested: for example, lists may contain other lists.

: Document structure

 Headers, footnote definitions, and named links give greater structure to a document. They may not be nested inside of blocks.

## Description

### Inline Syntax

Emphasis is written with underscores:
```markupPreview
Here's some _emphasized_ text
```
Emphasis can be nested by using more underscores for the outer emphasis:
```markupPreview
Here's some __emphasized text with _extra_ emphasis__ inside
```

Strong emphasis (bold) is written with asterisks:
```markupPreview
Here's some *bold* text
```

Hyperlinks consist of the link text in square brackets followed by the target in parentheses:
```markupPreview
The [Lean website](https://lean-lang.org)
```

```markupPreview
The [Lean website][lean]

[lean]: https://lean-lang.org
```

```markupPreview
The definition of `main`
```


TeX math can be included using a single or double dollar sign followed by code. Two dollar signs results in display-mode math, so `` $`\sum_{i=0}^{10} i` `` results in $`\sum_{i=0}^{10} i` while `` $$`\sum_{i=0}^{10} i` `` results in: $$`\sum_{i=0}^{10} i`

### Block Syntax

### Document Structure

## Differences from Markdown

This is a quick "cheat sheet" for those who are used to Markdown, documenting the differences.

### Syntax Errors

While Markdown includes a set of precedence rules to govern the meaning of mismatched delimiters (such as in `what _is *bold_ or emph*?`), these are syntax errors in Lean's markup.
Similarly, Markdown specifies that unmatched delimiters (such as `*` or `_`) should be included as characters, while Lean's markup requires explicit escaping of delimiters.

This is based on the principle that, for long-form technical writing, it's better to catch typos while writing than while reviewing the text later.

### Reduced Lookahead

In Markdown, whether `[this][here]` is a link depends on whether `here` is defined as a link reference target somewhere in the document.
In Lean's markup, it is always a link, and it is an error if `here` is not defined as a link target.

### Header Nesting

In Lean's markup, every document already has a title, so there's no need to use the highest level header (`#`) to specify one.
Additionally, all documents are required to use `#` for their top-level header, `##` for the next level, and so forth, because a single file may represent a section, a chapter, or even a whole book.
Authors should not need to maintain a global mapping from header levels to document structures, so Lean's markup automatically assigns these based on the structure of the document.

### Genre-Specific Extensions

Markdown has no standard way for specific tools or styles of writing to express domain- or {ref "genres"}[genre]-specific concepts.
Lean's markup provides standard syntaxes to use for this purpose, enabling compositional extensions.
