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
  prs := []

#doc (Manual) "Adaptation to Lean's Verso Parser" =>

Lean parses Verso markup, and Verso reads the syntax that it produces.

Document syntax reaches expanders as Lean's content tokens and views, which changes the types that extensions are written against:

* `InlineExpander` takes an `InlineView` and `BlockExpander` a `BlockView`, in place of the raw syntax of a single kind.

* `RoleExpander` takes an `Array VersoInline` and `DirectiveExpander` an `Array VersoBlock`.

* `CodeBlockExpander` takes a `VersoCodeBlock`, and the helpers that read content take the token that holds it, such as `VersoCode` and `VersoText`, in place of a `StrLit`.

* `VersoLiteral` is named `Literal`, and `decode` and `encode` are reached through it rather than exported on their own.

* `oneCodeStr`, `oneCodeStr?` and `oneCodeName` are deprecated in favor of Lean's `Lean.Doc.onlyCode`, together with `onlyCode?` and `onlyName`. Whitespace around a role's code argument is now ignored, content that is not code is reported at the first such element, and a wrong number of code elements is reported at the arguments together with the square brackets around them.

* `Verso.Parser` keeps the parsing that the elaborator uses, and the combinators that the document parser needed are gone.

A document opened by a run of colons reads to a bounded region.
The first line that begins with at least as many colons as the opener closes it, a longer run is an error, and a stray character in the contents is reported where it occurs.
