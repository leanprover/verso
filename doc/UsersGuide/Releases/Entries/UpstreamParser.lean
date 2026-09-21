/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 36, 0⟩
  breaking := true
  tag := "upstream-parser"
  prs := [989]

open Lean (Syntax StrLit)
open Lean.Doc (InlineView BlockView VersoInline VersoBlock VersoCodeBlock VersoText)
open Verso Doc.Elab

#doc (Manual) "Adaptation to Lean's Rewritten Verso Parser" =>

Verso markup is parsed by code that is part of Lean.
The upstream parser was rewritten to enable code formatting, with substantial improvements to error messages along the way.
Adapting to the new parser required changes in Verso.

Lean pull requests [#15604](https://github.com/leanprover/lean4/pull/15064), [#15211](https://github.com/leanprover/lean4/pull/15211), and [#15213](https://github.com/leanprover/lean4/pull/15213) rewrite Verso's parser.
This new parser tracks source information more accurately, which enables Lean's upcoming code formatter to be used for Verso documents.

Verso previously had conventions for representing Verso's syntax in Lean's {name}`Syntax` type.
This syntax was also defined in Lean, providing a way to pattern match on Verso syntax when writing extensions.
While this is still possible, the new fully-faithful representation has many details to get right and corner cases to remember, so most users should use a set of view types that capture the potential variation in inductive types.

Now, document syntax reaches expanders as Lean's own views, which changes the types that extensions are written against.
Additionally, some Verso functions have been replaced with their upstream equivalents:

* {name}`InlineExpander` takes an {name}`InlineView` and {name}`BlockExpander` a {name}`BlockView`, in place of the raw syntax of a single kind.

* {name}`RoleExpander` takes an {lean}`Array VersoInline` and {name}`DirectiveExpander` an {lean}`Array VersoBlock`.
  Role and directive expanders that need to recursively process their arguments should call {lean}`InlineView.of` or {lean}`BlockView.of` and then pattern match on the resulting views.

* {name}`CodeBlockExpander` takes a {name}`VersoCodeBlock`, and the helpers that read content take the token that holds it, such as `VersoCode` and {name}`VersoText`, in place of a {name}`StrLit`.

* A new type class {name}`Literal` allows the variety of literals that have replace {name}`StrLit` in the API to be processed using common functions, namely {name}`Literal.decode` and {name}`Literal.encode`.

* `oneCodeStr`, `oneCodeStr?` and `oneCodeName` are deprecated in favor of Lean's {name}`Lean.Doc.onlyCode`, and its Verso-specific related functions {name}`Verso.Doc.onlyCode?` and {name}`Verso.Doc.onlyName`. To harmonize with upstream Lean, whitespace around a role's code argument is now ignored.
