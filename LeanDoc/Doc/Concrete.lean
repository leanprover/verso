import Lean

import LeanDoc.Doc
import LeanDoc.Doc.Elab
import LeanDoc.Parser
import LeanDoc.SyntaxUtils

namespace LeanDoc.Doc.Concrete

open Lean Parser

open LeanDoc Parser SyntaxUtils Doc Elab

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
    let ((), st') ← DocElabM.run {headerContext := none, headerStack := #[]} <| for i in out do elabInline i
    let res := st'.stack
    elabTerm (← `(term| #[ $[$res],* ] )) none
  | _ => throwUnsupportedSyntax

#eval inlines!"Hello, *emph*"

def document : Parser where
  fn := rawFn <| blocks {maxDirective := some 6}

@[combinator_parenthesizer document] def document.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter document] def document.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous


elab "#docs" n:ident title:inlineStr ":=" ":::::::" text:document ":::::::" : command => open Lean Elab Command DocElabM in do
  let endTok := match ← getRef with | .node _ _ t => t.back?.get! | _ => panic! "Nothing"
  let endPos := endTok.getPos?.get!
  let .node _ _ blocks := text.raw
    | dbg_trace "nope {ppSyntax text.raw}" throwUnsupportedSyntax
  let ⟨`<low| [~_ ~(titleName@(.node _ _ titleParts))]>⟩ := title
    | dbg_trace "nope {ppSyntax title}" throwUnsupportedSyntax
  let (toc, st) ← liftTermElabM <| DocElabM.run (State.init titleName) <| do
    array for titleInline in titleParts do elabInline titleInline
    for b in blocks do
      elabBlock b
    closeSectionsUntil endTok 1
    let toc := (← get).headerStack[0]!.close endPos
    closeSectionsUntil endTok 0
    pure toc
  pushInfoLeaf <| .ofCustomInfo {stx := (← getRef) , value := Dynamic.mk toc}
  let #[stx] := st.stack
    | throwErrorAt n "Too many ({st.stack.size}) leftover stack elements! {st.stack.map ppSyntax}"
  -- dbg_trace "Syntax is {stx}"
  elabCommand (← `(def $n : Part := $stx))


elab "#doc" title:inlineStr "=>" text:document eof:eoi : term => open Lean Elab Term DocElabM in do
  let .node _ _ blocks := text.raw
    | dbg_trace "nope {ppSyntax text.raw}" throwUnsupportedSyntax
  let ⟨`<low| [~_ ~(titleName@(.node _ _ titleParts))]>⟩ := title
    | dbg_trace "nope {ppSyntax title}" throwUnsupportedSyntax
  let (toc, st) ← DocElabM.run (State.init titleName) <| do
    array for titleInline in titleParts do elabInline titleInline
    for b in blocks do
      elabBlock b
    closeSectionsUntil eof 1
    let toc := (← get).headerStack[0]!.close eof.raw.getTailPos?.get!
    closeSectionsUntil eof 0
    pure toc
  pushInfoLeaf <| .ofCustomInfo {stx := text, value := Dynamic.mk toc}
  let #[stx] := st.stack
    | throwErrorAt title "Too many ({st.stack.size}) leftover stack elements! {st.stack.map ppSyntax}"
  -- dbg_trace "Syntax is {stx}"
  elabTerm stx none
