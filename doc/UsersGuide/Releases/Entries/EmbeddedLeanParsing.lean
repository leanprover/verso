/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio Jesús Gallego Arias
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

set_option linter.verso.manual.headerTags false

release_note
  version := ⟨4, 37, 0⟩
  breaking := true
  tag := "embedded-lean-parsing"
  prs := [750, 1077]

#doc (Manual) "Parsing Embedded Lean from Source Regions" =>

Embedded Lean code and blog initialization headers are parsed directly from bounded regions of the original source, without constructing whitespace-padded copies.
The parser reuses the current file map and preserves absolute source positions.
This uses the parser APIs introduced in [Lean PR #15856](https://github.com/leanprover/lean4/pull/15856).

For a token whose source range excludes its delimiters, {name}`Verso.SyntaxUtils.parseSourceCategory` parses that region according to an extensible syntax category.
The token's positions select the source bytes; its stored value is not decoded.
Source normalization must precede assigning positions, as it does in Lean's frontend.
Invalid source ranges throw elaboration errors; ordinary parse failures return `Except.error`.

The existing standalone-string helpers and `parserInputString` remain available.

Blog example contexts now retain command state and start a fresh parser for each code region.
Extensions that match on `Verso.Genre.Blog.LeanExampleData.inline` should supply or match only the command state; the parser-state argument has been removed.
