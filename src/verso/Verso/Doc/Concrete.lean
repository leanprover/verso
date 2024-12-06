/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso.Doc
import Verso.Doc.Elab
import Verso.Doc.Elab.Incremental
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

def inlineStr := withAntiquot (mkAntiquot "inlineStr" `inlineStr) (inStrLit <| textLine)

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
  fn := atomicFn <| Verso.Parser.document (blockContext := {maxDirective := some 6})

@[combinator_parenthesizer document] def document.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter document] def document.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

/-- Advance the parser to EOF on failure so Lean doesn't try to parse further commands -/
def completeDocument : Parser where
  fn := (recoverFn Verso.Parser.document fun _ => skipFn) >> untilEoi
where
  untilEoi : ParserFn := fun c s =>
    s.setPos c.input.endPos

@[combinator_parenthesizer completeDocument] def completeDocument.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter completeDocument] def completeDocument.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous


open Lean.Elab Command in
partial def findGenreCmd : Syntax → Lean.Elab.Command.CommandElabM Unit
  | `($g:ident) => discard <| liftTermElabM <| realizeGlobalConstNoOverloadWithInfo g -- Don't allow it to become an auto-argument
  | `(($e)) => findGenreCmd e
  | _ => pure ()

open Lean.Elab Term in
partial def findGenreTm : Syntax → TermElabM Unit
  | `($g:ident) => discard <| realizeGlobalConstNoOverloadWithInfo g -- Don't allow it to become an auto-argument
  | `(($e)) => findGenreTm e
  | _ => pure ()


def saveRefs [Monad m] [MonadInfoTree m] (st : DocElabM.State) (st' : PartElabM.State) : m Unit := do
  for r in internalRefs st'.linkDefs st.linkRefs do
    for stx in r.syntax do
      pushInfoLeaf <| .ofCustomInfo {stx := stx , value := Dynamic.mk r}
  for r in internalRefs st'.footnoteDefs st.footnoteRefs do
    for stx in r.syntax do
      pushInfoLeaf <| .ofCustomInfo {stx := stx , value := Dynamic.mk r}

elab "#docs" "(" genre:term ")" n:ident title:inlineStr ":=" ":::::::" text:document ":::::::" : command => open Lean Elab Command PartElabM DocElabM in do
  findGenreCmd genre
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

elab "#doc" "(" genre:term ")" title:inlineStr "=>" text:completeDocument eoi : term => open Lean Elab Term PartElabM DocElabM in do
  findGenreTm genre
  let endPos := (← getFileMap).source.endPos
  let .node _ _ blocks := text.raw
    | dbg_trace "nope {ppSyntax text.raw}" throwUnsupportedSyntax
  let ⟨`<low| [~_ ~(titleName@(.node _ _ titleParts))]>⟩ := title
    | dbg_trace "nope {ppSyntax title}" throwUnsupportedSyntax
  let titleString := inlinesToString (← getEnv) titleParts
  let ((), st, st') ← PartElabM.run {} (.init titleName) <| do
    let mut errors := #[]
    setTitle titleString (← liftDocElabM <| titleParts.mapM elabInline)
    for b in blocks do
      try
        partCommand b
      catch e =>
        errors := errors.push e
    closePartsUntil 0 endPos
    for e in errors do
      match e with
      | .error stx msg => logErrorAt stx msg
      | oops@(.internal _ _) => throw oops
    pure ()
  let finished := st'.partContext.toPartFrame.close endPos
  pushInfoLeaf <| .ofCustomInfo {stx := (← getRef) , value := Dynamic.mk finished.toTOC}
  saveRefs st st'
  elabTerm (← `( ($(← finished.toSyntax genre st'.linkDefs st'.footnoteDefs) : Part $genre))) none


open Language

/--
The complete state of `PartElabM`, suitable for saving and restoration during incremental
elaboration
-/
structure DocElabSnapshotState where
  docState : DocElabM.State
  partState : PartElabM.State
  termState : Term.SavedState
deriving Nonempty

structure DocElabSnapshot where
  finished : Task DocElabSnapshotState
deriving Nonempty, TypeName

instance : IncrementalSnapshot DocElabSnapshot DocElabSnapshotState where
  getIncrState snap := snap.finished
  mkSnap := DocElabSnapshot.mk

instance : MonadStateOf DocElabSnapshotState PartElabM where
  get := getter
  set := setter
  -- Not great for linearity, but incrementality breaks that anyway and that's the only use case for
  -- this instance.
  modifyGet f := do
    let s ← getter
    let (val, s') := f s
    setter s'
    pure val
where
  getter := do pure ⟨← getThe _, ← getThe _,  ← saveState (m := TermElabM)⟩
  setter
    | ⟨docState, partState, termState⟩ => do
      set docState
      set partState
      -- SavedState.restore doesn't  restore enough state, so dig in!
      set termState.elab
      (show MetaM Unit from set termState.meta.meta)
      (show CoreM Unit from set termState.meta.core.toState)

open Lean.Parser.Command in
instance : Quote String (k := ``docComment) where
  quote str := ⟨.node .none ``docComment #[ .atom .none "/--", .atom .none (str ++ "-/")]⟩

elab (name := completeDoc) "#doc" "(" genre:term ")" title:inlineStr "=>" text:completeDocument eoi : command => open Lean Elab Term Command PartElabM DocElabM in do
  findGenreCmd genre
  let endPos := (← getFileMap).source.endPos
  let .node _ _ blocks := text.raw
    | dbg_trace "nope {ppSyntax text.raw}" throwUnsupportedSyntax
  let ⟨`<low| [~_ ~(titleName@(.node _ _ titleParts))]>⟩ := title
    | dbg_trace "nope {ppSyntax title}" throwUnsupportedSyntax
  let titleString := inlinesToString (← getEnv) titleParts
  let initState : PartElabM.State := .init titleName
  withTraceNode `Elab.Verso (fun _ => pure m!"Document AST elab") <|
    incrementallyElabCommand blocks
      (initAct := do setTitle titleString (← liftDocElabM <| titleParts.mapM elabInline))
      (endAct := fun ⟨st, st', _⟩ => withTraceNode `Elab.Verso (fun _ => pure m!"Document def") do
        let st' := st'.closeAll endPos
        let finished := st'.partContext.toPartFrame.close endPos
        pushInfoLeaf <| .ofCustomInfo {stx := (← getRef) , value := Dynamic.mk finished.toTOC}
        saveRefs st st'
        let n ← currentDocName
        let docName := mkIdentFrom title n
        let titleStr : TSyntax ``Lean.Parser.Command.docComment := quote titleString
        elabCommand (← `($titleStr:docComment def $docName : Part $genre := $(← finished.toSyntax' genre st'.linkDefs st'.footnoteDefs))))
      (handleStep := partCommand)
      (run := fun act => liftTermElabM <| Prod.fst <$> PartElabM.run {} initState act)

/--
Make the single elaborator for some syntax kind become incremental

This is useful because `elab` doesn't create an accessible name for the generated elaborator. It's
possible to predict it and apply the attribute, but this seems fragile - better to look it up.
Placing the attribute before `elab` itself doesn't work because the attribute ends up on the
`syntax` declaration. Seperate elaborators don't work if the syntax rule in question ends with an
EOF - `elab` provides a representation of it (which can be checked via `isMissing` to see if the
parser went all the way), but that's not present in the parser's own syntax objects. Quoting `eoi`
doesn't  work because the parser wants to read to the end of the file.
-/
scoped elab "elab" &"incremental" kind:ident : command =>
  open Lean Elab Command Term in do
  let k ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo kind
  let elabs := commandElabAttribute.getEntries (← getEnv) k
  match elabs with
  | [] => throwErrorAt kind "No elaborators for '{k}'"
  | [x] =>
    let elabName := mkIdentFrom kind x.declName
    elabCommand (← `(attribute [incremental] $elabName))
  | _ => throwErrorAt kind "Multiple elaborators for '{k}'"

elab incremental completeDoc
