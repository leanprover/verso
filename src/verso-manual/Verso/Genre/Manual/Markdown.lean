/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import MD4Lean

import Lean.Exception

import Verso.Doc

open MD4Lean
open Lean

namespace Verso.Genre.Manual.Markdown


def attrText : AttrText → Except String String
  | .normal str => pure str
  | .nullchar => throw "Null character"
  | .entity ent => throw s!"Unsupported entity {ent}"

def attr [Monad m] [MonadError m] (val : Array AttrText) : m Term := do
  match val.mapM attrText |>.map Array.toList |>.map String.join with
  | .error e => throwError e
  | .ok s => pure (quote s)

def attr' (val : Array AttrText) : Except String String := do
  match val.mapM attrText |>.map Array.toList |>.map String.join with
  | .error e => .error e
  | .ok s => pure s


partial def inlineFromMarkdown [Monad m] [MonadQuotation m] [MonadError m] : Text → m Term
  | .normal str | .br str | .softbr str => ``(Verso.Doc.Inline.text $(quote str))
  | .nullchar => throwError "Null character"
  | .del _ => throwError "Strikethrough"
  | .em txt => do ``(Verso.Doc.Inline.emph #[$[$(← txt.mapM inlineFromMarkdown)],*])
  | .strong txt => do ``(Verso.Doc.Inline.bold #[$[$(← txt.mapM inlineFromMarkdown)],*])
  | .a href _ _ txt => do ``(Verso.Doc.Inline.link #[$[$(← txt.mapM inlineFromMarkdown)],*] $(quote (← attr href)))
  | .latexMath m => ``(Verso.Doc.Inline.math Verso.Doc.MathMode.inline $(quote <| String.join m.toList))
  | .latexMathDisplay m =>  ``(Verso.Doc.Inline.math Verso.Doc.MathMode.display $(quote <| String.join m.toList))
  | .u .. => throwError "Underline"
  | .code str => ``(Verso.Doc.Inline.code $(quote <| String.join str.toList))
  | .entity ent => throwError s!"Unsupported entity {ent}"
  | .img .. => throwError s!"Image"
  | .wikiLink .. => throwError s!"Wiki-style link"

partial def inlineFromMarkdown' : Text → Except String (Doc.Inline g)
  | .normal str | .br str | .softbr str => pure <| .text str
  | .nullchar => .error "Null character"
  | .del _ => .error "Strikethrough"
  | .em txt => .emph <$> txt.mapM inlineFromMarkdown'
  | .strong txt => .bold <$> txt.mapM inlineFromMarkdown'
  | .a href _ _ txt => .link <$> txt.mapM inlineFromMarkdown' <*> attr' href
  | .latexMath m => pure <| .math .inline <| String.join m.toList
  | .latexMathDisplay m =>  pure <| .math .display <| String.join m.toList
  | .u .. => .error "Underline"
  | .code str => pure <| .code <| String.join str.toList
  | .entity ent => .error s!"Unsupported entity {ent}"
  | .img .. => .error s!"Image"
  | .wikiLink .. => .error s!"Wiki-style link"


partial def blockFromMarkdown [Monad m] [MonadQuotation m] [MonadError m] : MD4Lean.Block → m Term
  | .p txt => do ``(Verso.Doc.Block.para #[$[$(← txt.mapM inlineFromMarkdown)],*])
  | .blockquote bs => do ``(Verso.Doc.Block.blockquote #[$[$(← bs.mapM blockFromMarkdown)],*])
  | .code _ _ _ strs => do ``(Verso.Doc.Block.code $(quote <| String.join strs.toList))
  | .looseUl _ items => do ``(Verso.Doc.Block.ul #[$[$(← items.mapM looseItemFromMarkdown)],*])
  | .looseOl i _ items => do ``(Verso.Doc.Block.ol (Int.ofNat $(quote i)) #[$[$(← items.mapM looseItemFromMarkdown)],*])
  | .tightUl _ items => do
    let itemStx ← items.mapM tightItemFromMarkdown
    ``(Verso.Doc.Block.ul #[$itemStx,*])
  | .tightOl i _ items => do
    let itemStx ← items.mapM tightItemFromMarkdown
    ``(Verso.Doc.Block.ol (Int.ofNat $(quote i)) #[$itemStx,*])
  | .header .. => throwError "header"
  | .html .. => throwError "HTML"
  | .hr => throwError "Horizontal rule (thematic break)"
  | .table .. => throwError "Horizontal rule (thematic break)"
where
  looseItemFromMarkdown [Monad m] [MonadQuotation m] [MonadError m] (item : MD4Lean.Li MD4Lean.Block) : m Term := do
    if item.isTask then throwError "Tasks unsupported"
    else ``(Verso.Doc.ListItem.mk 0 #[$[$(← item.contents.mapM blockFromMarkdown)],*])
  tightItemFromMarkdown [Monad m] [MonadQuotation m] [MonadError m] (item : MD4Lean.Li MD4Lean.Text) : m Term := do
    if item.isTask then throwError "Tasks unsupported"
    else ``(Verso.Doc.ListItem.mk 0 #[Verso.Doc.Block.para #[$(← item.contents.mapM inlineFromMarkdown),*]])

partial def blockFromMarkdown' : MD4Lean.Block → Except String (Doc.Block g)
  | .p txt => .para <$> txt.mapM inlineFromMarkdown'
  | .blockquote bs => .blockquote <$> bs.mapM blockFromMarkdown'
  | .code _ _ _ strs => pure <| .code <| String.join strs.toList
  | .looseUl _ items => .ul <$> items.mapM looseItemFromMarkdown
  | .looseOl i _ items => .ol i <$> items.mapM looseItemFromMarkdown
  | .tightUl _ items =>
    .ul <$> items.mapM tightItemFromMarkdown
  | .tightOl i _ items =>
    .ol i <$> items.mapM tightItemFromMarkdown
  | .header .. => .error "header"
  | .html .. => .error "HTML"
  | .hr => .error "Horizontal rule (thematic break)"
  | .table .. => .error "Horizontal rule (thematic break)"
where
  looseItemFromMarkdown (item : MD4Lean.Li MD4Lean.Block) : Except String (Doc.ListItem _) := do
    if item.isTask then .error "Tasks unsupported"
    else .mk 0 <$> item.contents.mapM blockFromMarkdown'
  tightItemFromMarkdown (item : MD4Lean.Li MD4Lean.Text) : Except String (Doc.ListItem _) := do
    if item.isTask then .error "Tasks unsupported"
    else
      let inlines ← item.contents.mapM inlineFromMarkdown'
      pure <| .mk 0 #[.para inlines]
