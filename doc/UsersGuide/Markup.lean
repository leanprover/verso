import Verso.Genre.Manual

open Verso.Genre

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

TODO build an extension to test the parsing here

### Inline Syntax



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
