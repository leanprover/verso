/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Lean.DocString.View

public section

namespace Verso

open Lean

/--
A syntax kind whose tokens denote a string.

Each kind writes its string with delimiters and escapes of its own, so code that reads a literal's
text, or replaces it with new text, works at any of them.
-/
class Literal (k : SyntaxNodeKinds) where
  /-- The text that `stx` denotes. -/
  decode (stx : TSyntax k) : String
  /-- A token at `src`'s position that denotes `value`. -/
  encode (src : Syntax) (value : String) : TSyntax k

instance : Literal strLitKind where
  decode stx := stx.getString
  encode src value := Syntax.mkStrLit value (info := src.getHeadInfo)

instance : Literal ``Doc.Parser.versoText where
  decode stx := stx.getVersoText
  encode src value := Doc.mkVersoTextFrom src value

instance : Literal ``Doc.Parser.versoRef where
  decode stx := stx.getVersoRefName
  encode src value := Doc.mkVersoRefNameFrom src value

instance : Literal ``Doc.Parser.versoLinkUrl where
  decode stx := stx.getVersoLinkUrl
  encode src value := Doc.mkVersoLinkUrlFrom src value

instance : Literal ``Doc.Parser.versoLinkRefUrl where
  decode stx := stx.getVersoLinkRefUrl
  encode src value := Doc.mkVersoLinkRefUrlFrom src value

instance : Literal ``Doc.Parser.versoImageAlt where
  decode stx := stx.getVersoImageAlt
  encode src value := Doc.mkVersoImageAltFrom src value

instance : Literal ``Doc.Parser.versoCode where
  decode stx := stx.getVersoCode
  encode src value := Doc.mkVersoCodeFrom src value

instance : Literal ``Doc.Parser.versoCodeBlock where
  decode stx := stx.getVersoCodeBlock
  encode src value := Doc.mkVersoCodeBlockFrom src value
