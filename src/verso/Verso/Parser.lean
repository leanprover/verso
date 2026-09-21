/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
import Lean.Parser
public import Lean.Parser.Basic
public import Lean.Parser.Types

import Verso.Parser.Lean
public import Verso.SyntaxUtils
import Lean.DocString.Syntax
public import Lean.DocString.Parser

public section

namespace Verso.Parser

open Verso.SyntaxUtils
open Lean Parser

export Lean.Doc.Parser (skipFn ignoreFn)

scoped instance : Coe Char ParserFn where
  coe := chFn

instance : AndThen ParserFn where
  andThen p1 p2 := andthenFn p1 (p2 ())

instance : OrElse ParserFn where
  orElse p1 p2 := orelseFn p1 (p2 ())

/-- Like `satisfyFn`, but allows any escape sequence through -/
partial def satisfyEscFn (p : Char → Bool) (errorMsg : String := "unexpected character") : ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then s.mkEOIError
  else if c.get' i h == '\\' then
    let s := s.next' c i h
    let i := s.pos
    if h : c.atEnd i then s.mkEOIError
    else s.next' c i h
  else if p (c.get' i h) then s.next' c i h
  else s.mkUnexpectedError errorMsg

private def asStringAux (quoted : Bool) (startPos : String.Pos.Raw) (transform : String → String) : ParserFn := fun c s =>
  let input    := c
  let stopPos  := s.pos
  let leading  := c.mkEmptySubstringAt startPos
  let val      := input.extract startPos stopPos
  let val      := transform val
  let trailing := c.mkEmptySubstringAt stopPos
  let atom     :=
    mkAtom (SourceInfo.original leading startPos trailing stopPos) <|
      if quoted then val.quote else val
  s.pushSyntax atom

/-- Match an arbitrary Parser and return the consumed String in a `Syntax.atom`. -/
def asStringFn (p : ParserFn) (quoted := false) (transform : String → String := id ) : ParserFn := fun c s =>
  let startPos := s.pos
  let iniSz := s.stxStack.size
  let s := p c s
  if s.hasError then s
  else asStringAux quoted startPos transform c (s.shrinkStack iniSz)

def strFn (str : String) : ParserFn := asStringFn <| fun c s =>
  let rec go (iter : String.Legacy.Iterator) (s : ParserState) :=
    if iter.atEnd then s
    else
      let ch := iter.curr
      go iter.next <| satisfyFn (· == ch) ch.toString c s
  let iniPos := s.pos
  let iniSz := s.stxStack.size
  let s := go (String.Legacy.iter str) s
  if s.hasError then s.mkErrorAt s!"'{str}'" iniPos (some iniSz) else s

/-!
Verso's markup is Lean's docstring markup, so the productions below are `Lean.Doc.Parser`'s. They
produce the syntax that Verso's elaborators consume.
-/

export Lean.Doc.Parser (
  OrderedListType UnorderedListType InlineCtxt ListStyle BlockCtxt
  inlineTextCharFn blockOpenerFn valFn argEndWs argFn argsFn nameAndArgsFn
  textFn emphFn boldFn codeFn mathFn linkFn imageFn footnoteFn roleFn
  delimitedInlineFn inlineFn
  paraFn headerFn codeBlockFn directiveFn blockCommandFn linkRefFn footnoteRefFn
  listItemFn descItemFn blockquoteFn unorderedListFn orderedListFn definitionListFn
  blockFn blocksFn blocks1Fn documentFn
  metadataContents metadataBlockFn
  lookaheadOrderedListMarker lookaheadUnorderedListMarker)

/-- One or more inline elements. With `allowNewlines`, they may continue onto the following lines. -/
def textLine (allowNewlines := true) : ParserFn := many1Fn (inlineFn { allowNewlines })

/--
Some number of blank lines followed by zero or more blocks.

`documentFn` wraps the blocks in a node of its own, while Verso's elaborators consume the sequence
of blocks, so the wrapper is removed here.
-/
def document (blockContext : BlockCtxt := {}) : ParserFn := fun c s =>
  let iniSz := s.stxStack.size
  let s := documentFn blockContext c s
  if s.hasError || s.stxStack.size != iniSz + 1 then s
  else
    let stx := s.stxStack.back
    s.popSyntax.pushSyntax (stx.getArg 0)

end Verso.Parser

namespace Verso.Doc.Concrete
open Verso.Parser
open Verso.SyntaxUtils
open Lean Elab Term

public def stringToInlines [Monad m] [MonadFileMap m] [MonadError m] [MonadEnv m] [MonadQuotation m] (s : StrLit) : m (Array Syntax) :=
  withRef s do
    return (← parseMarkupStrLit textLine s).getArgs

open Lean Elab Term in
public def stringToBlocks [Monad m] [MonadFileMap m] [MonadError m] [MonadEnv m] [MonadQuotation m] (s : StrLit) : m (Array Syntax) :=
  withRef s do
    return (← parseMarkupStrLit (blocksFn {}) s).getArgs

end Verso.Doc.Concrete
