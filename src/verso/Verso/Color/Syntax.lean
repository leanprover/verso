/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

meta import Lean.Parser
meta import Lean.Parser.Types
public import Lean.Parser.Types
public meta import Lean.Parser.Basic
public import Lean.PrettyPrinter.Parenthesizer
public import Lean.PrettyPrinter.Formatter
public import Lean.Elab.Term
meta import Lean.PrettyPrinter
meta import Lean.Elab.Term
public meta import Verso.Color.Basic
public meta import Verso.Color.Widget

namespace Verso

public section

open Lean Parser PrettyPrinter

/-- The syntax node kind produced by the `colorHex` parser. -/
meta def colorHexKind : SyntaxNodeKind := `Verso.colorHex

private meta def isHexDigit (c : Char) : Bool :=
  if c.isDigit then true
  else if 'a' ≤ c ∧ c ≤ 'f' then true
  else if 'A' ≤ c ∧ c ≤ 'F' then true
  else false

/--
Parses a hexadecimal color: a `#` followed by the maximal run of hex digits (upper- or lowercase),
terminated by the first non-hex character or end of input. The run length is checked by the
elaborator, not the parser, in order to provide better error messages.
-/
private meta def colorHexFn : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let iniPos := s.pos
  let curr := c.get iniPos
  if curr != '#' then
    s.mkErrorAt "'#' to begin a color literal" iniPos initStackSz
  else
    let s := s.next c iniPos
    let s := takeWhileFn isHexDigit c s
    mkNodeToken colorHexKind iniPos true c s

/-- A parser for the `#`-prefixed hexadecimal section of a `color%` literal. -/
meta def colorHex : Parser :=
  withAntiquot (mkAntiquot "colorHex" colorHexKind) {
    fn := colorHexFn
    info := mkAtomicInfo "colorHex"
  }

@[combinator_parenthesizer colorHex]
meta def colorHex.parenthesizer : Parenthesizer := Parenthesizer.visitToken
@[combinator_formatter colorHex]
meta def colorHex.formatter : Formatter := Formatter.visitAtom colorHexKind

meta initialize register_parser_alias colorHex

/-- The hex digits of a `colorHex` syntax, without the leading `#`. -/
private meta def asHexString (stx : TSyntax colorHexKind) : String :=
  let val := (stx.raw.ifNode (·.getArg 0) (fun _ => stx.raw)).getAtomVal
  match val.toList with
  | '#' :: rest => String.ofList rest
  | cs => String.ofList cs

/--
A color literal: `color%#rgb`, `color%#rrggbb`, or `color%#rrggbbaa` (case-insensitive hex, no space
before the `#`). It is an ordinary term, usable anywhere a `Color` is expected, including in
structure-field defaults.
-/
syntax (name := colorLit) "color%" noWs colorHex : term

open Elab Term in
@[term_elab colorLit]
meta def elabColorLit : TermElab := fun stx expectedType? => do
  let hexStx := stx.getArg 1
  let hex := asHexString ⟨hexStx⟩
  let (r, g, b, a) ←
    match fromHexString hex with
    | .ok v => pure v
    | .error msg => throwErrorAt hexStx msg
  saveColorWidget (.rgba r g b a) stx
  let lit (n : UInt8) : Term := ⟨Syntax.mkNumLit (toString n.toNat)⟩
  elabTerm (← `(Verso.Color.rgba $(lit r) $(lit g) $(lit b) $(lit a))) expectedType?

end
