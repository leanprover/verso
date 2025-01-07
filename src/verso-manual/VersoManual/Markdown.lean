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

/--
Markdown documents in practice have unpredictable nesting of headers, so the nesting is provided
here as ordered handlers, rather than as a mapping from levels to handlers.

Because we're rendering Markdown in a Verso context that doesn't support nesting structure, will not
generate nested `Part`s, but rather some custom node or some formatted text.
-/
private structure HeaderHandlers (m : Type u → Type w) (block : Type u) (inline : Type v) : Type (max u v w) where
  levels : List (Array inline → m block) := []

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
  | .nullchar => throwError "Unexpected null character in parsed Markdown"
  | .del _ => throwError "Unexpected strikethrough in parsed Markdown"
  | .em txt => do ``(Verso.Doc.Inline.emph #[$[$(← txt.mapM inlineFromMarkdown)],*])
  | .strong txt => do ``(Verso.Doc.Inline.bold #[$[$(← txt.mapM inlineFromMarkdown)],*])
  | .a href _ _ txt => do ``(Verso.Doc.Inline.link #[$[$(← txt.mapM inlineFromMarkdown)],*] $(quote (← attr href)))
  | .latexMath m => ``(Verso.Doc.Inline.math Verso.Doc.MathMode.inline $(quote <| String.join m.toList))
  | .latexMathDisplay m =>  ``(Verso.Doc.Inline.math Verso.Doc.MathMode.display $(quote <| String.join m.toList))
  | .u txt => throwError "Unexpected underline around {repr txt} in parsed Markdown"
  | .code str => ``(Verso.Doc.Inline.code $(quote <| String.join str.toList))
  | .entity ent => throwError s!"Unsupported entity {ent} in parsed Markdown"
  | .img .. => throwError s!"Unexpected image in parsed Markdown"
  | .wikiLink .. => throwError s!"Unexpected wiki-style link in parsed Markdown"

partial def inlineFromMarkdown' : Text → Except String (Doc.Inline g)
  | .normal str | .br str | .softbr str => pure <| .text str
  | .nullchar => .error "Unepxected null character in parsed Markdown"
  | .del _ => .error "Unexpected strikethrough in parsed Markdown"
  | .em txt => .emph <$> txt.mapM inlineFromMarkdown'
  | .strong txt => .bold <$> txt.mapM inlineFromMarkdown'
  | .a href _ _ txt => .link <$> txt.mapM inlineFromMarkdown' <*> attr' href
  | .latexMath m => pure <| .math .inline <| String.join m.toList
  | .latexMathDisplay m =>  pure <| .math .display <| String.join m.toList
  | .u txt => .error s!"Unexpected underline around {repr txt} in parsed Markdown:"
  | .code str => pure <| .code <| String.join str.toList
  | .entity ent => .error s!"Unsupported entity {ent} in parsed Markdown"
  | .img .. => .error s!"Unexpected image in parsed Markdown"
  | .wikiLink .. => .error s!"Unexpected wiki-style link in parsed Markdown"

private structure MDState where
  /-- A mapping from document header levels to actual nesting levels -/
  inHeaders : List (Nat × Nat) := []
deriving Inhabited

private abbrev MDT m block inline α := ReaderT (HeaderHandlers m block inline) (StateT MDState m) α

instance [Monad m] [MonadError m] : MonadError (MDT m b i) where
  throw ex := fun _ρ _σ => throw ex
  tryCatch act handler := fun ρ σ => tryCatch (act ρ σ) (fun e => handler e ρ σ)
  getRef := fun _ρ σ => (·, σ) <$> getRef
  withRef stx act := fun ρ σ => withRef stx (act ρ σ)
  add stx msg := fun _ρ σ => (·, σ) <$> AddErrorMessageContext.add stx msg

private partial def getHeaderLevel [Monad m] (level : Nat) : MDT m b i Nat := do
  let hdrs := (← get).inHeaders
  match hdrs with
  | [] =>
    modify ({· with inHeaders := [(level, 0)]})
    pure 0
  | (docLevel, nesting) :: more =>
    if level < docLevel then
      modify ({· with inHeaders := more})
      getHeaderLevel level
    else if level = docLevel then
      pure nesting
    else
      modify ({· with inHeaders := (level, nesting + 1) :: hdrs})
      pure (nesting + 1)

private def getHeader  [Monad m] (level : Nat) : MDT m b i (Except String (Array i → m b)) := do
  let lvl ← getHeaderLevel level
  match (← read).levels.get? lvl with
  | none => pure (throw s!"Unexpected header with nesting level {lvl} in parsed Markdown")
  | some f => pure (pure f)

private partial def blockFromMarkdownAux [Monad m] [MonadQuotation m] [MonadError m] : MD4Lean.Block → MDT m Term Term Term
  | .p txt => do ``(Verso.Doc.Block.para #[$[$(← txt.mapM (inlineFromMarkdown ·))],*])
  | .blockquote bs => do ``(Verso.Doc.Block.blockquote #[$[$(← bs.mapM blockFromMarkdownAux )],*])
  | .code _ _ _ strs => do ``(Verso.Doc.Block.code $(quote <| String.join strs.toList))
  | .ul _ _ items => do ``(Verso.Doc.Block.ul #[$[$(← items.mapM itemFromMarkdown)],*])
  | .ol _ i _ items => do
    let itemStx ← items.mapM itemFromMarkdown
    ``(Verso.Doc.Block.ol (Int.ofNat $(quote i)) #[$itemStx,*])
  | .header level txt => do
    match (← getHeader level) with
    | .error e => throwError e
    | .ok h => do
      let inlines ← txt.mapM (inlineFromMarkdown ·)
      h inlines
  | .html .. => throwError "Unexpected literal HTML in parsed Markdown"
  | .hr => throwError "Unexpected horizontal rule (thematic break) in parsed Markdown"
  | .table .. => throwError "Unexpected table in parsed Markdown"
where
  itemFromMarkdown [Monad m] [MonadQuotation m] [MonadError m] (item : MD4Lean.Li MD4Lean.Block) : MDT m Term Term Term := do
    if item.isTask then throwError "Tasks unsupported"
    else ``(Verso.Doc.ListItem.mk #[$[$(← item.contents.mapM blockFromMarkdownAux)],*])


def blockFromMarkdown [Monad m] [MonadQuotation m] [MonadError m]
    (md : MD4Lean.Block)
    (handleHeaders : List (Array Term → m Term) := []) : m Term :=
  (·.fst) <$> blockFromMarkdownAux md ⟨handleHeaders⟩ {}

def strongEmphHeaders [Monad m] [MonadQuotation m] : List (Array Term → m Term) := [
  fun stxs => ``(Verso.Doc.Block.para #[Verso.Doc.Inline.bold #[$stxs,*]]),
  fun stxs => ``(Verso.Doc.Block.para #[Verso.Doc.Inline.emph #[$stxs,*]])
]

private partial def blockFromMarkdownAux' : MD4Lean.Block → MDT (Except String) (Doc.Block g) (Doc.Inline g) (Doc.Block g)
  | .p txt => .para <$> txt.mapM (inlineFromMarkdown' ·)
  | .blockquote bs => .blockquote <$> bs.mapM blockFromMarkdownAux'
  | .code _ _ _ strs => pure <| .code <| String.join strs.toList
  | .ul _ _ items => .ul <$> items.mapM itemFromMarkdown
  | .ol _ i _ items => .ol i <$> items.mapM itemFromMarkdown
  | .header level txt => do
    match (← getHeader level) with
    | .error e => throw e
    | .ok h => do
      let inlines ← txt.mapM (inlineFromMarkdown' ·)
      h inlines
  | .html .. => .error "Unexpected literal HTML in parsed Markdown"
  | .hr => .error "Unexpected horizontal rule (thematic break) in parsed Markdown"
  | .table .. => .error "Unexpected table in parsed Markdown"
where
  itemFromMarkdown (item : MD4Lean.Li MD4Lean.Block) : MDT (Except String) (Doc.Block g) (Doc.Inline g) (Doc.ListItem _) := do
    if item.isTask then .error "Tasks unsupported"
    else .mk <$> item.contents.mapM blockFromMarkdownAux'


def blockFromMarkdown'
    (md : MD4Lean.Block)
    (handleHeaders : List (Array (Doc.Inline g) → Except String (Doc.Block g)) := []) : Except String (Doc.Block g) :=
  (·.fst) <$> blockFromMarkdownAux' md ⟨handleHeaders⟩ {}

def strongEmphHeaders' : List (Array (Doc.Inline g) → Except String (Doc.Block g)) := [
  fun inls => pure <| .para #[.bold inls],
  fun inls => pure <| .para #[.emph inls]
]
