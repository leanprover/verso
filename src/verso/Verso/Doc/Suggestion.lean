/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean

namespace Verso.Doc.Suggestion

open Lean Elab Server RequestM

structure Suggestion where
  summary : String
  replacement : String
deriving TypeName

def saveSuggestion [Monad m] [MonadInfoTree m] (stx : Syntax) (summary replacement: String) : m Unit := do
  pushInfoLeaf <| .ofCustomInfo {stx := stx, value := Dynamic.mk (Suggestion.mk summary replacement) }

@[code_action_provider]
def provideSuggestions : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let startPos := text.lspPosToUtf8Pos params.range.start
  let endPos := text.lspPosToUtf8Pos params.range.end
  let suggestions := snap.infoTree.foldInfo (init := #[]) fun ctx info result => Id.run do
    let .ofCustomInfo ⟨stx, data⟩ := info | result
    let some suggestions := data.get? Suggestion | result
    let (some head, some tail) := (stx.getPos? true, stx.getTailPos? true) | result
    unless head ≤ endPos && startPos ≤ tail do return result
    result.push (ctx, head, tail, suggestions)
  pure <| suggestions.map fun (_, head, tail, ⟨summary, replacement⟩) =>
      {
      eager := {
        title := s!"Replace with {summary}",
        kind? := some "quickfix",
        edit? := some <| .ofTextDocumentEdit {
          textDocument := doc.versionedIdentifier,
          edits := #[{newText := replacement, range := ⟨text.utf8PosToLspPos head, text.utf8PosToLspPos tail⟩}]
        }
      }
    }
