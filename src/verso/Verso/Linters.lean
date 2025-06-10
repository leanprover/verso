/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Linter.Basic
import Lean.Meta.Hint
import Verso.Parser

set_option linter.missingDocs true

open Lean Linter Elab Command

/-- Generates curly-quote suggestions -/
register_option linter.typography.quotes : Bool := {
  defValue := false
  descr := "if true, generate curly quote suggestions"
}

/-- Generates dash suggestions -/
register_option linter.typography.dashes : Bool := {
  defValue := false
  descr := "if true, generate em and en dash suggestions"
}

namespace Verso.Linter

private inductive PunctuationState where
  | none
  | atBeginning (pos : String.Pos)
  | afterDigit

private def typographyLint [Monad m] [MonadOptions m] [MonadEnv m] : m Bool := do
  return getLinterValue linter.typography.quotes (← getLinterOptions) ||
    getLinterValue linter.typography.dashes (← getLinterOptions)

/--
Lints for ASCII that should be typographical Unicode, such as proper em dashes or quotes.
-/
def typography : Linter where
  run := withSetOptionIn fun stx => do
    unless (`Verso.Doc.Concrete).isPrefixOf stx.getKind do return
    unless (← typographyLint) do return
    let text ← getFileMap

    let suggest (what : String) (replacement : String)
        (linter : Lean.Option Bool)
        (pos : String.Pos) (stop : String.Pos := text.source.next pos) := do
      let strLit :=
        Syntax.mkStrLit (String.singleton (text.source.get pos))
          (info := .original {str := text.source, startPos := pos, stopPos := pos} pos {str := text.source, startPos := stop, stopPos := stop} stop)
        let h ← liftTermElabM <| MessageData.hint m!"Replace with Unicode" #[{suggestion := replacement}] (ref? := strLit)
        logLint linter strLit (m!"Use {what} ('{replacement}')" ++ h)

    discard <| stx.replaceM fun
      | `(inline|$s:str) => do
        if let some ⟨start, stop⟩ := s.raw.getRange? then
          let mut state : PunctuationState :=
            if start == 0 || text.source.get (text.source.prev start) ∈ ['\n', ' '] then
              .atBeginning (text.source.prev start)
            else
              .none
          let mut iter : String.Iterator := ⟨text.source, start⟩
          while h : iter.hasNext ∧ iter.pos ≤ stop do
            let here := iter.pos
            let c := iter.curr' h.1
            iter := iter.next' h.1
            match state, c with
            | _, ' ' | _, '\n' =>
              state := .atBeginning here
            | .atBeginning _, '"' =>
              state := .none
              suggest "curly quotes" "“" linter.typography.quotes here
            | _, '"' =>
              state := .none
              if h : iter.hasNext then
                if iter.curr' h ∈ [' ', '\n', '.', ',', ':', ';', '?', '!', '}', ')', ']'] then
                  suggest "curly quotes" "”" linter.typography.quotes here
            | _, '-' =>
              let s : Substring := {str := text.source, startPos := here, stopPos := stop}
              let dashesSpaces := s.takeWhile fun c => c == '-' || c.isWhitespace
              let dashes := dashesSpaces.takeWhile (· == '-')
              let dashCount := dashes.stopPos.byteIdx - dashes.startPos.byteIdx
              if dashCount == 3 then
                let start := if let .atBeginning p := state then p else here
                suggest "an em dash" "—" linter.typography.dashes start dashesSpaces.stopPos
              else if dashCount == 2 then
                match state with
                | .afterDigit =>
                  suggest "an en dash" "–" linter.typography.dashes here dashesSpaces.stopPos
                | .atBeginning p =>
                  suggest "an em dash" "—" linter.typography.dashes p dashesSpaces.stopPos
                | .none =>
                  suggest "an em dash" "—" linter.typography.dashes here dashesSpaces.stopPos
              else if dashCount == 1 then
                match state with
                | .afterDigit =>
                  if text.source.get dashesSpaces.stopPos |>.isDigit then
                    suggest "an en dash" "–" linter.typography.dashes here dashesSpaces.stopPos
                | .atBeginning p =>
                  if dashesSpaces.stopPos != dashes.stopPos then
                    suggest "an em dash" "—" linter.typography.dashes p dashesSpaces.stopPos
                | _ => pure ()
              state := .none
              iter := {iter with i := dashesSpaces.stopPos}
            | _, _ =>
              state := if c.isDigit then .afterDigit else .none
        pure none
      | _ => pure none

initialize addLinter typography
