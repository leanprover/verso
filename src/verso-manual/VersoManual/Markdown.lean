/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import MD4Lean

import Lean.Exception

import Verso.Doc

import VersoManual.Basic

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

structure MDContext (m : Type u → Type w) (block : Type u) (inline : Type u) : Type (max u w) where
  headerHandlers : HeaderHandlers m block inline
  elabInlineCode : Option (Option String → String → m inline)
  elabBlockCode : Option (Option String → Option String → String → m block)

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

private structure MDState where
  /-- A mapping from document header levels to actual nesting levels -/
  inHeaders : List (Nat × Nat) := []
deriving Inhabited

private abbrev MDT m block inline α := ReaderT (MDContext m block inline) (StateT MDState m) α

instance {block inline} [Monad m] : MonadLift m (MDT m block inline) where
  monadLift act := fun _ s => act <&> (·, s)

instance {block inline} [Monad m] [AddMessageContext m] : AddMessageContext (MDT m block inline) where
  addMessageContext msg := (addMessageContext msg : m _)


instance {block inline} [AddMessageContext m] [Monad m] [MonadError m] : MonadError (MDT m block inline) where
  throw e := throw (m := m) e
  tryCatch a b := fun r s => do
    tryCatch (a r s) fun e => b e r s

private def lastWord (str : String) : Option String :=
  let words := str |>.split (!·.isAlpha) |>.filter (!·.isEmpty)
  words.getLast?

partial def inlineFromMarkdown [Monad m] [MonadQuotation m] [AddMessageContext m] [MonadError m] : Text → StateT (Option String) (MDT m Term Term) Term
  | .normal str | .br str | .softbr str => do
    (lastWord str).forM fun w => do
      set (some w.toLower)
    ``(Verso.Doc.Inline.text $(quote str))
  | .nullchar => throwError "Unexpected null character in parsed Markdown"
  | .del _ => throwError "Unexpected strikethrough in parsed Markdown"
  | .em txt => do ``(Verso.Doc.Inline.emph #[$[$(← txt.mapM inlineFromMarkdown)],*])
  | .strong txt => do ``(Verso.Doc.Inline.bold #[$[$(← txt.mapM inlineFromMarkdown)],*])
  | .a href _ _ txt => do ``(Verso.Doc.Inline.link #[$[$(← txt.mapM inlineFromMarkdown)],*] $(quote (← attr href)))
  | .latexMath m => do
    set (none : Option String)
    ``(Verso.Doc.Inline.math Verso.Doc.MathMode.inline $(quote <| String.join m.toList))
  | .latexMathDisplay m => do
    set (none : Option String)
    ``(Verso.Doc.Inline.math Verso.Doc.MathMode.display $(quote <| String.join m.toList))
  | .u txt => throwError "Unexpected underline around {repr txt} in parsed Markdown"
  | .code strs => do
    let str := String.join strs.toList
    if let some f := (← read).elabInlineCode then
      f (← get) str
    else
      ``(Verso.Doc.Inline.code $(quote str))
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
  match (← read).headerHandlers.levels[lvl]? with
  | none => pure (throw s!"Unexpected header with nesting level {lvl} in parsed Markdown")
  | some f => pure (pure f)

private partial def blockFromMarkdownAux [Monad m] [AddMessageContext m] [MonadQuotation m] [MonadError m] : MD4Lean.Block → MDT m Term Term Term
  | .p txt => do
    let inlines ← (txt.mapM (inlineFromMarkdown ·)).run' none
    ``(Verso.Doc.Block.para #[$inlines,*])
  | .blockquote bs => do ``(Verso.Doc.Block.blockquote #[$[$(← bs.mapM blockFromMarkdownAux )],*])
  | .code info lang _ strs => do
    let info? := (attr' info).toOption
    let lang? := (attr' lang).toOption
    let str := String.join strs.toList
    if let some f := (← read).elabBlockCode then
      f info? lang? str
    else
      ``(Verso.Doc.Block.code $(quote str))
  | .ul _ _ items => do ``(Verso.Doc.Block.ul #[$[$(← items.mapM itemFromMarkdown)],*])
  | .ol _ i _ items => do
    let itemStx ← items.mapM itemFromMarkdown
    ``(Verso.Doc.Block.ol (Int.ofNat $(quote i)) #[$itemStx,*])
  | .header level txt => do
    match (← getHeader level) with
    | .error e => throwError e
    | .ok h => do
      let inlines ← (txt.mapM (inlineFromMarkdown ·)).run' none
      h inlines
  | .html .. => throwError "Unexpected literal HTML in parsed Markdown"
  | .hr => throwError "Unexpected horizontal rule (thematic break) in parsed Markdown"
  | .table .. => throwError "Unexpected table in parsed Markdown"
where
  itemFromMarkdown [Monad m] [MonadQuotation m] [MonadError m] (item : MD4Lean.Li MD4Lean.Block) : MDT m Term Term Term := do
    if item.isTask then throwError "Tasks unsupported"
    else ``(Verso.Doc.ListItem.mk #[$[$(← item.contents.mapM blockFromMarkdownAux)],*])


def blockFromMarkdown [Monad m] [MonadQuotation m] [MonadError m] [AddMessageContext m]
    (md : MD4Lean.Block)
    (handleHeaders : List (Array Term → m Term) := [])
    (elabInlineCode : Option (Option String → String → m Term) := none)
    (elabBlockCode : Option (Option String → Option String → String → m Term) := none) : m Term :=
  let ctxt := {headerHandlers := ⟨handleHeaders⟩, elabInlineCode, elabBlockCode}
  (·.fst) <$> blockFromMarkdownAux md ctxt {}

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
    (handleHeaders : List (Array (Doc.Inline g) → Except String (Doc.Block g)) := [])
    (elabInlineCode : Option (Option String → String → Except String (Doc.Inline g)) := none)
    (elabBlockCode : Option (Option String → Option String → String → Except String (Doc.Block g)) := none) :
  Except String (Doc.Block g) :=
  (·.fst) <$> blockFromMarkdownAux' md ⟨⟨handleHeaders⟩, elabInlineCode, elabBlockCode⟩ {}

def strongEmphHeaders' : List (Array (Doc.Inline g) → Except String (Doc.Block g)) := [
  fun inls => pure <| .para #[.bold inls],
  fun inls => pure <| .para #[.emph inls]
]

private partial def stringFromMarkdownText : Text → Except String String
  | .normal str | .br str | .softbr str => pure str
  | .nullchar => .error "Unepxected null character in parsed Markdown"
  | .del _ => .error "Unexpected strikethrough in parsed Markdown"
  | .em txt => arrToStr <| txt.mapM stringFromMarkdownText
  | .strong txt => arrToStr <| txt.mapM stringFromMarkdownText
  | .a _ _ _ txt => arrToStr <| txt.mapM stringFromMarkdownText
  | .latexMath m => pure <| String.join m.toList
  | .latexMathDisplay m =>  pure <| String.join m.toList
  | .u txt => .error s!"Unexpected underline around {repr txt} in parsed Markdown:"
  | .code str => pure <| String.join str.toList
  | .entity ent => .error s!"Unsupported entity {ent} in parsed Markdown"
  | .img .. => .error s!"Unexpected image in parsed Markdown"
  | .wikiLink .. => .error s!"Unexpected wiki-style link in parsed Markdown"
where
  arrToStr (x : Except String (Array String)) : Except String String :=
    return String.join (← x).toList

open Verso.Doc.Elab

/--
Updates the active sections given a new header with `level`.
-/
private partial def closeSections (level : Nat) : MDT PartElabM b i Unit := do
  let hdrs := (← getThe MDState).inHeaders
  match hdrs with
  | [] => modifyThe MDState ({· with inHeaders := [(level, 0)]})
  | (docLevel, nesting) :: more =>
    if level ≤ docLevel then
      if let some ctxt' := (← getThe PartElabM.State).partContext.close default then -- FIXME: source position!
        modifyThe PartElabM.State fun st => {st with partContext := ctxt'}
        closeSections level
      if level < docLevel then
        modifyThe MDState ({· with inHeaders := more})
    else
      modifyThe MDState ({· with inHeaders := (level, nesting + 1) :: hdrs})

private partial def partFromMarkdownAux : MD4Lean.Block → MDT PartElabM Term Term Unit
  | .header level txt => do
    closeSections level
    let txtStxs ← txt.mapM inlineFromMarkdown |>.run' none
    let titleTexts ← match txt.mapM stringFromMarkdownText with
      | .ok t => pure t
      | .error e => throwError m!"Invalid Markdown in header:\n{e}"
    let titleText := titleTexts.foldl (· ++ ·) ""
    PartElabM.push {
      titleSyntax := quote (k := `str) titleText
      expandedTitle := some (titleText, txtStxs)
      metadata := none
      blocks := #[]
      priorParts := #[]
    }
  | b => do
    PartElabM.addBlock (← blockFromMarkdownAux b)

/--
Adds blocks from Markdown, treating top-level headers as new parts.

Note that `handleHeaders` is still used for elaborating headers that appear
nested within blocks (e.g., blockquotes).

`currentHeaderLevels` gives a list of headers within which elaboration is
occurring and which can be terminated by the current elaboration. Typically,
these are taken from a previous iteration of `partFromMarkdown`, but they can
also be specified manually as `(headerLevel, nestingLevel)` pairs.
-/
def partFromMarkdown
    (md : MD4Lean.Block)
    (currentHeaderLevels : List (Nat × Nat) := [])
    (handleHeaders : List (Array Term → PartElabM Term) := [])
    (elabInlineCode : Option (Option String → String → PartElabM Term) := none)
    (elabBlockCode : Option (Option String → Option String → String → PartElabM Term) := none) : PartElabM (List (Nat × Nat)) := do
  let ctxt := {headerHandlers := ⟨handleHeaders⟩, elabInlineCode, elabBlockCode}
  let (_, { inHeaders }) ← (partFromMarkdownAux md |>.run ctxt |>.run {inHeaders := currentHeaderLevels})
  return inHeaders
