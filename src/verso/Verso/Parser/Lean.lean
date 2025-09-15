/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/

/- This file contains modified versions of the Lean token parsers that
 don't consume trailing whitespace. These changes need to be
 upstreamed if we figure out how to make whitespace configurable in
 the parser framework, or perhaps it could be refactored to have two
 layers. Please don't blame the authors.-/

import Lean.Parser

open Lean Parser Syntax

namespace Verso.Parser

def docMkNodeToken (n : SyntaxNodeKind) (startPos : String.Pos) : ParserFn := fun c s => Id.run do
  if s.hasError then
    return s
  let stopPos   := s.pos
  let leading   := c.mkEmptySubstringAt startPos
  let val       := c.extract startPos stopPos
  -- let s         := whitespace c s
  let wsStopPos := s.pos
  let trailing  := c.substring (startPos := stopPos) (stopPos := wsStopPos)
  let info      := SourceInfo.original leading startPos trailing stopPos
  s.pushSyntax (Syntax.mkLit n val info)


partial def docStrLitFnAux (startPos : String.Pos) : ParserFn := fun c s =>
  let i     := s.pos
  if h : c.atEnd i then s.mkUnexpectedErrorAt "unterminated string literal" startPos
  else
    let curr := c.get' i h
    let s    := s.setPos (c.next' i h)
    if curr == '\"' then
      docMkNodeToken strLitKind startPos c s
    else if curr == '\\' then andthenFn quotedCharFn (docStrLitFnAux startPos) c s
    else docStrLitFnAux startPos c s


def docStrLitFn : ParserFn := fun c s =>
  let i     := s.pos
  let curr  := c.get i
  if c.atEnd i then s.mkEOIError ["string literal"]
  else if curr == '\"' then
    docStrLitFnAux i c (s.next c i)
  else s.mkUnexpectedError s!"'{curr}'"


def docBinNumberFn (startPos : String.Pos) : ParserFn := fun c s =>
  let s := takeWhile1Fn (fun c => c == '0' || c == '1') "binary number" c s
  mkNodeToken numLitKind startPos c s

def docOctalNumberFn (startPos : String.Pos) : ParserFn := fun c s =>
  let s := takeWhile1Fn (fun c => '0' ≤ c && c ≤ '7') "octal number" c s
  mkNodeToken numLitKind startPos c s

def docHexNumberFn (startPos : String.Pos) : ParserFn := fun c s =>
  let s := takeWhile1Fn (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) "hexadecimal number" c s
  mkNodeToken numLitKind startPos c s

def docDecimalNumberFn (startPos : String.Pos) (c : ParserContext) : ParserState → ParserState := fun s =>
  let s     := takeWhileFn (fun c => c.isDigit) c s
  let i     := s.pos
  let curr  := c.get i
  if curr == '.' || curr == 'e' || curr == 'E' then
    let s := parseOptDot s
    let s := parseOptExp s
    docMkNodeToken scientificLitKind startPos c s
  else
    docMkNodeToken numLitKind startPos c s
where
  parseOptDot s :=
    let i     := s.pos
    let curr  := c.get i
    if curr == '.' then
      let i    := c.next i
      let curr := c.get i
      if curr.isDigit then
        takeWhileFn (fun c => c.isDigit) c (s.setPos i)
      else
        s.setPos i
    else
      s

  parseOptExp s :=
    let i     := s.pos
    let curr  := c.get i
    if curr == 'e' || curr == 'E' then
      let i    := c.next i
      let i    := if c.get i == '-' || c.get i == '+' then c.next i else i
      let curr := c.get i
      if curr.isDigit then
        takeWhileFn (fun c => c.isDigit) c (s.setPos i)
      else
        s.mkUnexpectedError "missing exponent digits in scientific literal"
    else
      s

def docNumLitFn : ParserFn := fun c s =>
  let startPos := s.pos
  if c.atEnd startPos then s.mkEOIError ["numeral"]
  else if h : c.atEnd startPos then s.mkEOIError
  else
    let curr := c.get' startPos h
    if curr == '0' then
      let i    := c.next' startPos h
      let curr := c.get i
      if curr == 'b' || curr == 'B' then
        docBinNumberFn startPos c (s.next c i)
      else if curr == 'o' || curr == 'O' then
        docOctalNumberFn startPos c (s.next c i)
      else if curr == 'x' || curr == 'X' then
        docHexNumberFn startPos c (s.next c i)
      else
        docDecimalNumberFn startPos c (s.setPos i)
    else if curr.isDigit then
      docDecimalNumberFn startPos c (s.next c startPos)
    else
      s.mkError "numeral"

def docMkIdResult (startPos : String.Pos) (val : Name) : ParserFn := fun c s =>
  let stopPos         := s.pos
  let rawVal          := c.substring startPos stopPos
  let trailingStopPos := s.pos
  let leading         := c.mkEmptySubstringAt startPos
  let trailing        := c.substring (startPos := stopPos) (stopPos := trailingStopPos)
  let info            := SourceInfo.original leading startPos trailing stopPos
  let atom            := mkIdent info rawVal val
  s.pushSyntax atom

partial def docIdentFn (reportAs : String := "identifier") : ParserFn :=
  let rec parse (startPos : String.Pos) (r : Name) : ParserFn:= fun c s =>
    let i     := s.pos
    if h : c.atEnd i then
      s.mkEOIError [reportAs]
    else
      let curr := c.get' i h
      if isIdBeginEscape curr then
        let startPart := c.next' i h
        let s         := takeUntilFn isIdEndEscape c (s.setPos startPart)
        if h : c.atEnd s.pos then
          s.mkUnexpectedErrorAt "unterminated identifier escape" startPart
        else
          let stopPart  := s.pos
          let s         := s.next' c s.pos h
          let r : Name  := .str r (c.extract startPart stopPart)
          if isIdCont c s then
            let s := s.next c s.pos
            parse startPos r c s
          else
            docMkIdResult startPos r c s
      else if isIdFirst curr then
        let startPart := i
        let s         := takeWhileFn isIdRest c (s.next c i)
        let stopPart  := s.pos
        let r : Name  := .str r (c.extract startPart stopPart)
        if isIdCont c s then
          let s := s.next c s.pos
          parse startPos r c s
        else
          docMkIdResult startPos r c s
      else
        s.mkErrorAt reportAs startPos
  fun c s =>
    let startPos := s.pos
    parse startPos .anonymous c s
