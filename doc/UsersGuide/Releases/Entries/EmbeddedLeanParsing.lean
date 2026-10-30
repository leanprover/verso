/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio Jesús Gallego Arias
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 37, 0⟩
  breaking := true
  tag := "embedded-lean-parsing"
  prs := [750, 1077]

#doc (Manual) "Parsing Embedded Lean from Source Spans" =>

Embedded Lean code and blog initialization headers are parsed directly from bounded spans of the original source, without constructing whitespace-padded copies.
This requires the Lean parser APIs introduced in [Lean PR #15856](https://github.com/leanprover/lean4/pull/15856).

The parser helpers in `Verso.SyntaxUtils` change accordingly:

* `parserInputString` is removed. Use {name}`Verso.SyntaxUtils.strLitInputContext` to obtain a bounded input context and starting position for source syntax.

* {name}`Verso.SyntaxUtils.runParserCategory` now takes a category name and source syntax in a monad that supplies the environment, options, and file map. Use {name}`Verso.SyntaxUtils.runParserCategoryString` to parse decoded strings instead.

* `runParserCategory'` is replaced by {name}`Verso.SyntaxUtils.runParserCategoryGen` with {name}`Verso.SyntaxUtils.runParserCategory.toSyntaxErrors` as its error conversion function.
