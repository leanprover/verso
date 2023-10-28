import Lean

import LeanDoc.Doc
import LeanDoc.Doc.Elab
import LeanDoc.Parser
import LeanDoc.SyntaxUtils

namespace LeanDoc.Doc.Concrete

open Lean Parser

open LeanDoc Parser SyntaxUtils Doc Elab

def document : Parser where
  fn := rawFn <| blocks {maxDirective := some 6}

@[combinator_parenthesizer document] def document.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinator_formatter document] def document.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

elab "#docs" n:ident title:str ":=" ":::::::" text:document ":::::::" : command => open Lean Elab Command in do
  let .node _ _ blocks := text.raw
    | dbg_trace "nope {ppSyntax text.raw}" throwUnsupportedSyntax
  let ((), st) ← liftTermElabM <| DocElabM.run {headerContext := some {currentLevel := 0, startIndex := 0, inPrelude := some 1}, headerStack := #[0]} <| do
    DocElabM.push <| ← ``(#[Inline.text $title])
    for b in blocks do
      elabBlock b
    closeSectionsUntil 0
  let #[stx] := st.stack
    | throwErrorAt n "Too many ({st.stack.size}) leftover stack elements! {st.stack.map ppSyntax}"
  -- dbg_trace "Syntax is {stx}"
  elabCommand (← `(def $n : Part := $stx))


elab "#doc" title:str "=>" text:document eoi : term => open Lean Elab Term in do
  let .node _ _ blocks := text.raw
    | dbg_trace "nope {ppSyntax text.raw}" throwUnsupportedSyntax
  let ((), st) ← DocElabM.run {headerContext := some {currentLevel := 0, startIndex := 0, inPrelude := some 1}, headerStack := #[0]} <| do
    DocElabM.push <| ← ``(#[Inline.text $title])
    for b in blocks do
      elabBlock b
    closeSectionsUntil 0
  let #[stx] := st.stack
    | throwErrorAt title "Too many ({st.stack.size}) leftover stack elements! {st.stack.map ppSyntax}"
  -- dbg_trace "Syntax is {stx}"
  elabTerm stx none
