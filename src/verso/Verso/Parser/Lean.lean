/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/

module
public import Lean.Parser


public section

open Lean Parser Syntax

namespace Verso.Parser


partial def docStrLitFnAux (startPos : String.Pos) : ParserFn := fun c s =>
  let i     := s.pos
  if h : c.atEnd i then s.mkUnexpectedErrorAt "unterminated string literal" startPos
  else
    let curr := c.get' i h
    let s    := s.setPos (c.next' i h)
    if curr == '\"' then
      mkNodeToken strLitKind startPos false c s
    else if curr == '\\' then andthenFn quotedCharFn (docStrLitFnAux startPos) c s
    else docStrLitFnAux startPos c s


def docStrLitFn : ParserFn := fun c s =>
  let i     := s.pos
  let curr  := c.get i
  if c.atEnd i then s.mkEOIError ["string literal"]
  else if curr == '\"' then
    docStrLitFnAux i c (s.next c i)
  else s.mkUnexpectedError s!"'{curr}'"


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
        binNumberFn startPos false c (s.next c i)
      else if curr == 'o' || curr == 'O' then
        octalNumberFn startPos false c (s.next c i)
      else if curr == 'x' || curr == 'X' then
        hexNumberFn startPos false c (s.next c i)
      else
        decimalNumberFn startPos false c (s.setPos i)
    else if curr.isDigit then
      decimalNumberFn startPos false c (s.next c startPos)
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
