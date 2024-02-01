/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean

import Verso.Doc
import Verso.Doc.Elab
import Verso.Doc.Elab.Monad
import Verso.Doc.Lsp
import Verso.Parser
import Verso.SyntaxUtils

namespace Verso.Doc.Concrete

open Lean Parser

open Verso Parser SyntaxUtils Doc Elab

defmethod ParserFn.inStringLiteral (p : ParserFn) : ParserFn := fun c s =>
  let s' := strLitFn c s
  if s'.hasError then s'
  else
    let strLit : TSyntax `str := ⟨s'.stxStack.back⟩
    let afterQuote := s.next c.input s.pos
    let iniSz := afterQuote.stxStack.size
    let s'' := adaptUncacheableContextFn (replaceInputFrom s.pos strLit.getString) p c {afterQuote with pos := s.pos}
    if s''.hasError then s'' -- TODO update source locations for string decoding
    else
      let out := s''.stxStack.extract iniSz s''.stxStack.size
      let s'' := {s' with stxStack := s'.stxStack ++ out}
      s''.mkNode nullKind iniSz
where
  replaceInputFrom (p : String.Pos) new (c : ParserContextCore) := {c with input := c.input.extract 0 p ++ new }

def eosFn : ParserFn := fun c s =>
  let i := s.pos
  if c.input.atEnd i then s
  else s.mkError "end of string literal"


def inStrLit (p : ParserFn) : Parser where
  fn := p.inStringLiteral

@[combinator_parenthesizer inStrLit] def inStrLit.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter inStrLit] def inStrLit.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

def inlineStr := inStrLit <| textLine

elab "inlines!" s:inlineStr : term => open Lean Elab Term in
  match s.raw with
  | `<low| [~_ ~(.node _ _ out) ] > => do
    let (tms, _) ← DocElabM.run {} (.init (← `(foo))) <| out.mapM elabInline
    elabTerm (← `(term| #[ $[$tms],* ] )) none
  | _ => throwUnsupportedSyntax

set_option pp.rawOnError true

/--
info: #[Inline.text "Hello, ", Inline.emph #[Inline.bold #[Inline.text "emph"]]] : Array (Inline Genre.none)
-/
#guard_msgs in
#check (inlines!"Hello, _*emph*_" : Array (Inline .none))

def document : Parser where
  fn := rawFn <| atomicFn <| Verso.Parser.document (blockContext := {maxDirective := some 6})

@[combinator_parenthesizer document] def document.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter document] def document.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

partial def findGenre [Monad m] [MonadInfoTree m] [MonadResolveName m] [MonadEnv m] [MonadError m] : Syntax → m Unit
  | `($g:ident) => discard <| resolveGlobalConstNoOverloadWithInfo g -- Don't allow it to become an auto-argument
  | `(($e)) => findGenre e
  | _ => pure ()

def saveRefs [Monad m] [MonadInfoTree m] (st : DocElabM.State) (st' : PartElabM.State) : m Unit := do
  for r in internalRefs st'.linkDefs st.linkRefs do
    for stx in r.syntax do
      pushInfoLeaf <| .ofCustomInfo {stx := stx , value := Dynamic.mk r}
  for r in internalRefs st'.footnoteDefs st.footnoteRefs do
    for stx in r.syntax do
      pushInfoLeaf <| .ofCustomInfo {stx := stx , value := Dynamic.mk r}

elab "#docs" "(" genre:term ")" n:ident title:inlineStr ":=" ":::::::" text:document ":::::::" : command => open Lean Elab Command PartElabM DocElabM in do
  findGenre genre
  let endTok :=
    match ← getRef with
    | .node _ _ t =>
      match t.back? with
      | some x => x
      | none => panic! "No final token!"
    | _ => panic! "Nothing"
  let endPos := endTok.getPos!
  let .node _ _ blocks := text.raw
    | dbg_trace "nope {ppSyntax text.raw}" throwUnsupportedSyntax
  let ⟨`<low| [~_ ~(titleName@(.node _ _ titleParts))]>⟩ := title
    | dbg_trace "nope {ppSyntax title}" throwUnsupportedSyntax
  let titleString := inlinesToString (← getEnv) titleParts
  let ((), st, st') ← liftTermElabM <| PartElabM.run {} (.init titleName) <| do
    setTitle titleString (← liftDocElabM <| titleParts.mapM elabInline)
    for b in blocks do partCommand b
    closePartsUntil 0 endPos
    pure ()
  let finished := st'.partContext.toPartFrame.close endPos
  pushInfoLeaf <| .ofCustomInfo {stx := (← getRef) , value := Dynamic.mk finished.toTOC}
  saveRefs st st'

  elabCommand (← `(def $n : Part $genre := $(← finished.toSyntax genre st'.linkDefs st'.footnoteDefs)))


elab "#doc" "(" genre:term ")" title:inlineStr "=>" text:document eof:eoi : term => open Lean Elab Term PartElabM DocElabM in do
  findGenre genre
  let endPos := eof.raw.getTailPos?.get!
  let .node _ _ blocks := text.raw
    | dbg_trace "nope {ppSyntax text.raw}" throwUnsupportedSyntax
  let ⟨`<low| [~_ ~(titleName@(.node _ _ titleParts))]>⟩ := title
    | dbg_trace "nope {ppSyntax title}" throwUnsupportedSyntax
  let titleString := inlinesToString (← getEnv) titleParts
  let ((), st, st') ← PartElabM.run {} (.init titleName) <| do
    setTitle titleString (← liftDocElabM <| titleParts.mapM elabInline)
    for b in blocks do partCommand b
    closePartsUntil 0 endPos
    pure ()
  let finished := st'.partContext.toPartFrame.close endPos
  pushInfoLeaf <| .ofCustomInfo {stx := (← getRef) , value := Dynamic.mk finished.toTOC}
  saveRefs st st'
  elabTerm (← `( ($(← finished.toSyntax genre st'.linkDefs st'.footnoteDefs) : Part $genre))) none


macro "%doc" moduleName:ident : term =>
  pure <| mkIdentFrom moduleName <| docName moduleName.getId

macro "%docName" moduleName:ident : term =>
  let n := mkIdentFrom moduleName (docName moduleName.getId) |>.getId
  pure <| quote n


def currentDocName [Monad m] [MonadEnv m] : m Name := do
  pure <| docName <| (← Lean.MonadEnv.getEnv).mainModule


elab "#doc" "(" genre:term ")" title:inlineStr "=>" text:document eof:eoi : command => open Lean Elab Term Command PartElabM DocElabM in do
  findGenre genre
  if eof.raw.isMissing then
    throwError "Syntax error prevents processing document"
  else
    let endPos := eof.raw.getTailPos?.get!
    let .node _ _ blocks := text.raw
      | dbg_trace "nope {ppSyntax text.raw}" throwUnsupportedSyntax
    let ⟨`<low| [~_ ~(titleName@(.node _ _ titleParts))]>⟩ := title
      | dbg_trace "nope {ppSyntax title}" throwUnsupportedSyntax
    let titleString := inlinesToString (← getEnv) titleParts
    let ((), st, st') ← liftTermElabM <| PartElabM.run {} (.init titleName) <| do
      setTitle titleString (← liftDocElabM <| titleParts.mapM elabInline)
      for b in blocks do partCommand b
      closePartsUntil 0 endPos
      pure ()
    let finished := st'.partContext.toPartFrame.close endPos
    pushInfoLeaf <| .ofCustomInfo {stx := (← getRef) , value := Dynamic.mk finished.toTOC}
    saveRefs st st'
    let docName ← mkIdentFrom title <$> currentDocName
    elabCommand (← `(def $docName : Part $genre := $(← finished.toSyntax genre st'.linkDefs st'.footnoteDefs)))
