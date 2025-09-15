/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Parser
import Verso.Instances.Deriving

namespace Verso.Genre.Blog

abbrev LexedText.Highlighted := Array (Option String × String)

structure LexedText where
  name : String
  content : LexedText.Highlighted
deriving Repr, Inhabited, BEq, DecidableEq, Lean.Quote

namespace LexedText

open Lean Parser

-- In the absence of a proper regexp engine, abuse ParserFn here
structure Highlighter where
  name : String
  lexer : ParserFn
  tokenClass : Syntax → Option String

def highlight (hl : Highlighter) (str : String) : IO LexedText := do
  let mut out : Highlighted := #[]
  let mut unHl : Option String := none
  let env ← mkEmptyEnvironment
  let ictx := mkInputContext str "<input>"
  let pmctx : ParserModuleContext := {env := env, options := {}}
  let mut s := mkParserState str
  repeat
    if str.atEnd s.pos then
      if let some txt := unHl then
        out := out.push (none, txt)
      break
    let s' := hl.lexer.run ictx pmctx {} s
    if s'.hasError then
      let c := str.get! s.pos
      unHl := unHl.getD "" |>.push c
      s := {s with pos := s.pos + c}
    else
      let stk := s'.stxStack.extract 0 s'.stxStack.size
      if stk.size ≠ 1 then
        unHl := unHl.getD "" ++ str.extract s.pos s'.pos
        s := s'.restore 0 s'.pos
      else
        let stx := stk[0]!
        match hl.tokenClass stx with
        | none => unHl := unHl.getD "" ++ str.extract s.pos s'.pos
        | some tok =>
          if let some ws := unHl then
            out := out.push (none, ws)
            unHl := none
          out := out.push (some tok, str.extract s.pos s'.pos)
        s := s'.restore 0 s'.pos
  pure ⟨hl.name, out⟩

def token (kind : Name) (p : ParserFn) : ParserFn :=
  nodeFn kind <| Lean.Doc.Parser.ignoreFn p
