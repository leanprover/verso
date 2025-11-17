/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Linter.Basic
import Lean.Meta.Hint
import Verso.Parser
import Lean.Elab.Command
import Lean.Data.Options

set_option linter.missingDocs true

open Lean Linter Elab Command
open Lean.Doc.Syntax

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

/-- Generates asterisk and underscore minimization suggestions -/
register_option linter.verso.markup.emph : Bool := {
  defValue := true
  descr := "if true, generate suggestions to minimize markup for emphasis"
}

/-- Generates backtick minimization suggestions -/
register_option linter.verso.markup.code : Bool := {
  defValue := true
  descr := "if true, generate suggestions to minimize markup for inline code elements"
}

/-- Generates backtick minimization suggestions for code blocks -/
register_option linter.verso.markup.codeBlock : Bool := {
  defValue := true
  descr := "if true, generate suggestions to minimize markup for code block elements"
}

namespace Verso.Linter

private inductive PunctuationState where
  | none
  | atBeginning (pos : String.Pos.Raw)
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
        (pos : String.Pos.Raw) (stop : String.Pos.Raw := pos.next text.source) := do
      let strLit :=
        Syntax.mkStrLit (String.singleton (pos.get text.source))
          (info := .original {str := text.source, startPos := pos, stopPos := pos} pos {str := text.source, startPos := stop, stopPos := stop} stop)
        let h ← liftTermElabM <| MessageData.hint m!"Replace with Unicode" #[{suggestion := replacement}] (ref? := strLit)
        logLint linter strLit (m!"Use {what} ('{replacement}')" ++ h)

    discard <| stx.replaceM fun
      | `(inline|$s:str) => do
        if let some ⟨start, stop⟩ := s.raw.getRange? then
          let mut state : PunctuationState :=
            if start == 0 || (start.prev text.source).get text.source ∈ ['\n', ' '] then
              .atBeginning (start.prev text.source)
            else
              .none
          let mut iter : String.Legacy.Iterator := ⟨text.source, start⟩
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
              let s : Substring.Raw := {str := text.source, startPos := here, stopPos := stop}
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
                  if dashesSpaces.stopPos.get text.source |>.isDigit then
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

private def longestRunOf (string : Substring.Raw) (char : Char) : Nat := Id.run do
  let mut best := 0
  let mut curr : Option Nat := none
  let mut iter := { String.Legacy.iter string.str with i := string.startPos }
  while h : iter.hasNext ∧ iter.i < string.stopPos do
    let c := iter.curr' h.1
    iter := iter.next' h.1
    if c == char then
      if let some n := curr then
        curr := some (n + 1)
      else
        curr := some 1
    else
      if let some n := curr then
        best := max n best
        curr := none
  if let some n := curr then
    best := max n best
  return best

private def lintDelimited (linter : Lean.Option Bool) (text : FileMap) (tk1 tk2 : Syntax) (delimChar : Char) (minimal : Nat := 1) : CommandElabM Unit := do
  unless getLinterValue linter (← getLinterOptions) do return
  let some ⟨start1, stop1⟩ := tk1.getRange?
    | pure ()
  let some ⟨start2, stop2⟩ := tk2.getRange?
    | pure ()
  let opener := start1.extract text.source stop1
  let closer := start2.extract text.source stop2
  let length := opener.length
  if closer.length ≠ length then return
  if length ≤ minimal then return
  let contents := { text.source.toSubstring with startPos := stop1, stopPos := start2 }
  let biggest := longestRunOf contents delimChar
  if biggest < length - 1 then
    let delim := String.ofList (List.replicate (max (biggest + 1) minimal) delimChar)
    let replacement := (delim ++ contents.toString ++ delim)
    let strLit :=
      Syntax.mkStrLit (start1.extract text.source stop2)
        (info := .original {str := text.source, startPos := start1, stopPos := start1} start1 {str := text.source, startPos := stop2, stopPos := stop2} stop2)
    let h ← liftTermElabM <| MessageData.hint m!"Use the minimal number of '{delimChar}'s" #[{suggestion := replacement}] (ref? := strLit)
    let note :=
      if opener == "**" then MessageData.note m!"In Verso, emphasis is indicated with `_` and bold with `*`."
      else m!""
    logLint linter strLit (m!"Unnecessary '{delimChar}'" ++ note ++ h)

/--
Lints for unnecessary extra `*` and `_` on emhasis inlines
-/
def emphasisMinimization : Linter where
  run := withSetOptionIn fun stx => do
    unless (`Verso.Doc.Concrete).isPrefixOf stx.getKind do return
    unless getLinterValue linter.verso.markup.emph (← getLinterOptions) do return

    let text ← getFileMap

    discard <| stx.replaceM fun
      | `(inline|_[%$tk1 $e* ]%$tk2) => do
        lintDelimited linter.verso.markup.emph text tk1 tk2 '_'
        pure none
      | `(inline|*[%$tk1 $e* ]%$tk2) => do
        lintDelimited linter.verso.markup.emph text tk1 tk2 '*'
        pure none
      | _ => pure none

initialize addLinter emphasisMinimization

/--
Lints for unnecessary extra backticks on code
-/
def codeMinimization : Linter where
  run := withSetOptionIn fun stx => do
    unless (`Verso.Doc.Concrete).isPrefixOf stx.getKind do return
    let opts ← getLinterOptions
    unless getLinterValue linter.verso.markup.code opts || getLinterValue linter.verso.markup.codeBlock opts do return

    let text ← getFileMap

    discard <| stx.replaceM fun
      | `(inline|code(%$tk1 $_ )%$tk2) => do
        lintDelimited linter.verso.markup.code text tk1 tk2 '`'
        pure none
      | `(block|```%$tk1 $[$_ $_*]? | $_ ```%$tk2) => do
        lintDelimited linter.verso.markup.codeBlock text tk1 tk2 '`' (minimal := 3)
        pure none
      | _ => pure none

initialize addLinter codeMinimization
