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


open Lean.Parser

public partial def htmlCommentContentsFn : ParserFn := fun c s =>
  let startPos := s.pos
  if h : c.atEnd s.pos then
    s.mkEOIError ["HTML comment end"]
  else
    if c.get' s.pos h == '-' then
      let s := s.setPos (c.next' s.pos h)
      if h' : ¬c.atEnd s.pos then
        if c.get' s.pos h' == '-' then
          let s := s.setPos (c.next' s.pos h')
          if h'' : ¬c.atEnd s.pos then
            if c.get' s.pos h'' == '>' then
              s.setPos (c.next' s.pos h'')
            else htmlCommentContentsFn c <| s.setPos (c.next' startPos h)
          else s.mkEOIError ["HTML comment end"]
        else htmlCommentContentsFn c <| s.setPos (c.next' startPos h)
      else s.mkEOIError ["HTML comment end"]
    else htmlCommentContentsFn c <| s.setPos (c.next' startPos h)

public def htmlCommentContents : Parser where
  fn := rawFn htmlCommentContentsFn (trailingWs := true)

open Lean PrettyPrinter Formatter Parenthesizer

@[combinator_parenthesizer htmlCommentContents]
public def htmlCommentContents.parenthesizer := visitToken

@[combinator_formatter htmlCommentContents]
public def htmlCommentContents.formatter := visitAtom Name.anonymous
