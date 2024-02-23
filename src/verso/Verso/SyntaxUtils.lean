/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean

import Verso.Method

namespace Verso.SyntaxUtils

open Lean Parser
open Std.Format

defmethod Syntax.getPos! (stx : Syntax) : String.Pos :=
  if let some pos := stx.getPos? then pos else panic! s!"No position for {stx}"

defmethod SourceInfo.getPos! (info : SourceInfo) : String.Pos :=
  if let some pos := info.getPos? then pos else panic! s!"No position for {repr info}"

def ppSyntax (stx : Syntax) : Std.Format := .nest 2 <| stx.formatStx (some 50) false

def ppStack (elts : Array Syntax) (number : Bool := false) : Std.Format := Id.run do
  let mut stk : Format := .nil
  match elts.size with
  | 0 => stk := " empty"
  | 1 => stk := "  " ++ ppSyntax (elts.get! 0)
  | n =>
    for i in [0:n] do
      let tm := ppSyntax (elts.get! i)
      let num := if number then .text s!"[{i}] " else .nil
      stk := stk ++ .group (" • " ++ num ++ nest 2 (.group tm)) ++ line
  pure stk

defmethod ParserFn.test (p : ParserFn) (input : String) : IO String := do
  let ictx := mkInputContext input "<input>"
  let env : Environment ← mkEmptyEnvironment
  let pmctx : ParserModuleContext := {env := env, options := {}}
  let s' := p.run ictx pmctx (getTokenTable env) (mkParserState input)
  let stk := ppStack <| s'.stxStack.extract 0 s'.stxStack.size

  let remaining : String := if s'.pos ≥ input.endPos then "All input consumed." else s!"Remaining:\n{repr (input.extract s'.pos input.endPos)}"

  if s'.allErrors.isEmpty then
    return s!"Success! Final stack:\n{stk.pretty 50}\n{remaining}"
  else if let #[(p, _, err)] := s'.allErrors then
    return s!"Failure: {err}\nFinal stack:\n{stk.pretty 50}\nRemaining: {repr $ input.extract p input.endPos}"
  else
    let mut errors := ""
    for (p, _, e) in s'.allErrors do
      errors := errors ++ s!"  @{p}: {toString e}\n    {repr <| input.extract p input.endPos}\n"
    return s!"{s'.allErrors.size} failures:\n{errors}\nFinal stack:\n{stk.pretty 50}"

defmethod ParserFn.test! (p : ParserFn) (input : String) : IO Unit :=
  p.test input >>= IO.println

defmethod ParserFn.parseString [Monad m] [MonadError m] [MonadEnv m] (p : ParserFn) (input : String) : m Syntax := do
  let ictx := mkInputContext input "<input>"
  let env ← getEnv
  let pmctx : ParserModuleContext := {env := env, options := {}}
  let s' := p.run ictx pmctx (getTokenTable env) (mkParserState input)
  let stk := s'.stxStack.extract 0 s'.stxStack.size
  if let some err := s'.errorMsg then
    throwError err.toString
  if h : ¬stk.size = 1 then
    throwError "Expected single item in parser stack, got {ppStack stk}"
  else
    have : stk.size = 1 := Classical.byContradiction h
    have : 0 < stk.size := by simp_arith [*]
    pure stk[0]

scoped instance : Quote SourceInfo `term where
  quote
   | .none =>
     ⟨Syntax.mkCApp ``SourceInfo.none #[]⟩
   | .synthetic pos endPos canonical =>
     ⟨Syntax.mkCApp ``SourceInfo.synthetic #[quotePos pos, quotePos endPos, quote canonical]⟩
   | .original leading pos trailing pos' =>
     ⟨Syntax.mkCApp ``SourceInfo.original #[quote leading, quotePos pos, quote trailing, quotePos pos']⟩
where
  quotePos : String.Pos → TSyntax `term
    | ⟨idx⟩ => Syntax.mkCApp `String.Pos.mk #[quote idx]


/-- A more convenient concrete syntax for low-level syntax objects,
without needing to involve the Lean parser. Useful when working at the
ParserFn level.-/
declare_syntax_cat lowStx
syntax str : lowStx
syntax "[" lowStx* "]" : lowStx
syntax "(" ident lowStx* ")" : lowStx
/-- Embed a term into syntax -/
syntax "~" term:100 : lowStx
/-- Embed a string atom into syntax -/
syntax "~~" term:100 : lowStx

/-- Embedded low-level syntax -/
syntax "`<low|" lowStx ">" : term
macro_rules
  | `( `<low| $s:str > ) => ``(Syntax.atom $(quote s.raw.getHeadInfo) $(quote s.getString))
  | `( `<low| [ $stx* ] > ) => ``(Syntax.node SourceInfo.none nullKind #[ $[`<low| $stx > ],* ] )
  | `( `<low| ( $id $stx* ) > ) => ``(Syntax.node SourceInfo.none $(quote id.getId) #[ $[`<low| $stx > ],* ] )
  | `( `<low| ~$e > ) => ``(($e : Syntax))
  | `( `<low| ~~$e > ) => ``(Syntax.atom _ $e)
