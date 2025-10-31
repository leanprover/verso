/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Parser.Types
public import Lean.DocString.Parser
public import Lean.PrettyPrinter.Formatter
public import Lean.PrettyPrinter.Parenthesizer

namespace Verso.Output.Html

public abbrev attributeNameKind := `Verso.Output.Html.attributeName

open Lean.Parser
open Lean.Doc.Parser

public def attributeNameFn : ParserFn :=
  atomicFn <|
    nodeFn attributeNameKind <|
      asStringFn <| andthenFn (satisfyFn versoAttributeNameChar) (manyFn attributeNameCharFn)
where
  -- A slight divergence from the spec for the sake of quasiquotation syntax:
  -- attribute names can't start with a few special characters that the spec allows but that
  -- are very obscure and make parser errors much worse.
  versoAttributeNameChar (c : Char) : Bool := c ∉ ['{', '}', '<', '"', '\''] && attributeNameChar c
  -- https://html.spec.whatwg.org/multipage/syntax.html#attributes-2
  attributeNameChar (c : Char) : Bool :=
    !(isControl c) && c ∉ [' ', '"', '\'', '>', '/', '='] && !(isNonChar c)
  -- https://infra.spec.whatwg.org/#control
  isControl (c : Char) :=
    let n := c.toNat
    n ≥ 0x007f && n ≤ 0x009f
  -- https://infra.spec.whatwg.org/#noncharacter
  isNonChar (c : Char) :=
    let n := c.toNat
    (n ≥ 0xfdd0 && n ≤ 0xfdef) ||
    n ∈ [0xFFFE, 0xFFFF, 0x1FFFE, 0x1FFFF, 0x2FFFE, 0x2FFFF, 0x3FFFE, 0x3FFFF, 0x4FFFE,
      0x4FFFF, 0x5FFFE, 0x5FFFF, 0x6FFFE, 0x6FFFF, 0x7FFFE, 0x7FFFF, 0x8FFFE, 0x8FFFF,
      0x9FFFE, 0x9FFFF, 0xAFFFE, 0xAFFFF, 0xBFFFE, 0xBFFFF, 0xCFFFE, 0xCFFFF, 0xDFFFE,
      0xDFFFF, 0xEFFFE, 0xEFFFF, 0xFFFFE, 0xFFFFF, 0x10FFFE, 0x10FFFF]
  attributeNameCharFn := satisfyFn attributeNameChar "attribute name"


def attributeNameNoAntiquot : Parser where
  fn := andthenFn attributeNameFn (takeWhileFn Char.isWhitespace)

public def attributeName : Parser :=
  withAntiquot (mkAntiquot "attributeName" attributeNameKind) attributeNameNoAntiquot

open Lean PrettyPrinter Parenthesizer Formatter

@[combinator_parenthesizer attributeName]
public def attributeName.parenthesizer := visitToken

@[combinator_formatter attributeName]
public def attributeName.formatter := visitAtom Name.anonymous

public def _root_.Lean.TSyntax.getAttributeName (stx : TSyntax attributeNameKind) : String :=
  if let ⟨.node _ _ #[.atom _ name]⟩ := stx then
    name
  else panic! "Not an attribute name"
